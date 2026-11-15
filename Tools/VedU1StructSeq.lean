import Lean
import Tools.VedU1Contract
import Tools.VedU1Loop
import Tools.VedU1StructSeqTac

/-!
# Structure result with registers (`Signal.loop`), several output ports

Generated (untrusted) proof script for `U1Stmt C M f` when `f` is a statement TERM (the bundled lambda
of `Tools/VedU1StructOut.lean` / the product entry) rather than a constant, and the module has registers.
Not packed: the contract keeps one output port per field (docs: reviewer conditions of
`sparkle-ved-struct-seq`); `outputs_of_step` quantifies over ALL ports, so the proof is

* one loop invariant `R` (the loop path's: register `n` of the module is the `toNat` of the loop-state
  component it implements, by induction on the cycle; the loop is read off the value of the whole
  bundled tuple `(applyIns … f).val s`, in which every field's projection of the loop occurs);
* the step: the module's next registers satisfy `R` at `s + 1`, and EVERY port's value equals
  `srcOf C f ins port s`, one conjunct per port (`List.mem_cons` over the port list), closed by the
  same closing tactics as the packed script (`Tools/VedU1MultiSeq.lean`).

It lives below `Tools/VedU1Entry.lean` (which imports it, for the standard entry's dispatch), so it takes
the five names the checker registers as plain `Name`s and uses the `ved_ss_*` tactics.
-/

namespace Tools.VedU1StructSeq

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Loop Tools.VedU1StructSeqTac
open Lean Meta Elab Term

/-- Debugging/controls only: stop the generated script after stage `k` and print the goals. -/
register_option ved.sseq.dbg : Nat := {
  defValue := 0
  descr := "ved.sseq.dbg: stop the structure-with-registers script after stage k (0: off)"
}

/-- The generated (untrusted) script for `U1Stmt C M f` where `f` is the statement TERM (the bundled
lambda `fun xs => bundle2 (D xs).f₁ (bundle2 …)` of a structure / product result, or any term of the
table's type) and `C`'s module has the registers `regs` (name, width) of `Signal.loop`s.  Every output
port of the contract is closed: ONE loop invariant ("register n = toNat of the loop-state component"), and
the module's value of EACH port is compared with `srcOf C f ins <port> s` (one conjunct per port). -/
def structLoopScript (contractN modN outsN bodyN : Name) (F : Name) (fStx : Term) (regs : List (String × Nat))
    (helpers : Array Name) : TermElabM Syntax := do
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let C := mkCIdent contractN
  let M := mkCIdent modN
  let O := mkCIdent outsN
  let B := mkCIdent bodyN
  let fI := mkCIdent F
  -- defined in `Tools.VedU1Entry` (which imports this file): named, not quoted
  let oStep := mkCIdent `Tools.VedU1Entry.outputs_of_step
  let f : Term := fStx
  let k := regs.length
  let hs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hreg{i}")
  let rNames := (regs.map fun r => Syntax.mkStrLit r.1).toArray
  let rWidths := (regs.map fun r => Syntax.mkNumLit (toString r.2)).toArray
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let hinI := mkIdent `hin
  let hrstI := mkIdent `hrst
  let hR := mkIdent `hR
  let vI := mkIdent `vsrc
  let hv := mkIdent `hvsrc
  let hsAll : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let ex1 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ hsAll)
  let ex2 : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems (hsA ++ hsAll.push (← `(Lean.Parser.Tactic.simpLemma| $hrstI:ident)))
  let exHelp : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
    Syntax.TSepArray.ofElems hsA
  let pats ← (hs.toList).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  let hPat : TSyntax `rcasesPat ← match pats with
    | [] => `(rcasesPat| _)
    | _ => `(rcasesPat| ⟨$[$(pats.toArray)],*⟩)
  let mut tacs : Array (TSyntax `tactic) := #[]
  let timed := ved.sseq.dbg.get (← getOptions) == 97
  let wrap (t : TSyntax `tactic) : TermElabM (TSyntax `tactic) :=
    if timed then `(tactic| ved_ss_timed $t) else pure t
  tacs := tacs.push (← wrap (← `(tactic| intro $insI hok $sI st mems $hR)))
  tacs := tacs.push (← wrap (← `(tactic| have $hinI := hok.1 $sI)))
  tacs := tacs.push (← wrap (← `(tactic| have $hrstI := hok.2 $sI)))
  tacs := tacs.push (← wrap (← `(tactic| simp (config := { maxSteps := 2000000 }) [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at $hinI:ident $hrstI:ident)))
  tacs := tacs.push (← wrap (← `(tactic| simp only [$O:ident, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq])))
  tacs := tacs.push (← wrap (← `(tactic| obtain ⟨$vI, $hv⟩ : ∃ v, v = (applyIns ($C).table.ins ($C).inNames $insI $f).val $sI := ⟨_, rfl⟩)))
  tacs := tacs.push (← wrap (← `(tactic| ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $exHelp,*] at $hv:ident)))
  tacs := tacs.push (← wrap (← `(tactic| ved_ss_R $insI [$rNames,*] $rWidths,*)))
  tacs := tacs.push (← wrap (← `(tactic| clear $hv)))
  -- ONE register: the invariant is the equation itself (no conjunction to take apart)
  if hs.size == 1 then
    tacs := tacs ++ #[← wrap (← `(tactic| have $(hs[0]!):ident := $hR)), ← wrap (← `(tactic| clear $hR))]
  else
    tacs := tacs.push (← wrap (← `(tactic| obtain $hPat := $hR)))
  let closing ← if ved.sseq.dbg.get (← getOptions) == 96
    then `(tactic| all_goals (ved_ss_leafwise <;> (first | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod] | fail "leaf failed here")))
    else if ved.sseq.dbg.get (← getOptions) == 98
    then `(tactic| all_goals (ved_ss_timed (first
        | (ved_ss_leafwise <;> ved_ss_timed (ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod]))
        | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])))
    else if ved.sseq.dbg.get (← getOptions) == 99
    then `(tactic| all_goals (first | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod] | fail "ved_ss_loop_close failed here"))
    else `(tactic| all_goals (first
        | (ved_ss_leafwise <;> ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])
        | ved_ss_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod]))
  let stages : Array (Array (TSyntax `tactic)) := #[
    #[← `(tactic| ved_ss_unfold [$exHelp,*] ($sI + 1))],
    #[← `(tactic| ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $ex1,*])],
    #[← `(tactic| ved_ss_gen $sI)],
    #[← `(tactic| all_goals refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩),
      ← `(tactic| all_goals ved_ss_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident, Signal.fst, Signal.snd, $ex2,*]),
      ← `(tactic| all_goals try (repeat' apply And.intro))],
    #[← `(tactic| all_goals (try ved_ss_wide_simp [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_bv]))],
    #[← `(tactic| all_goals (try ved_bit_simp))],
    #[← `(tactic| all_goals (try ved_or_lit))],
    #[← `(tactic| all_goals (try ved_pack_simp))],
    #[← `(tactic| all_goals (try ved_ss_xor_ones))],
    #[← `(tactic| all_goals (try ved_bits_facts)), ← `(tactic| all_goals (try ved_mul_facts)),
      ← `(tactic| all_goals (try ved_pack_simp)),
      ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])),
      ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat]))],
    -- the one-bit logic again: the register fields are now plain values, so `x < 2` side conditions of
    -- `a ||| b` / `a &&& b` between comparisons (`inHdr := is1 ||| is2 ||| …`) are provable
    #[← `(tactic| all_goals (try ved_bit_simp))],
    -- a goal comparing a narrow state value with several literals is split on the state value
    #[← `(tactic| all_goals (try ved_ss_state_split))],
    #[closing]]
  let dbg := ved.sseq.dbg.get (← getOptions)
  if dbg == 50 then
    tacs := tacs.push (← `(tactic| ved_ss_unfold1 [$exHelp,*] ($sI + 1)))
  let stop ← `(tactic| (trace_state; fail "stopped at debug stage"))
  if dbg == 1 || (dbg ≥ 50 && dbg < 96 && !(dbg ≥ 91 && dbg ≤ 94)) then tacs := tacs.push stop
  else
    for k in [0:stages.size] do
      if dbg == 0 || dbg == 96 || dbg == 97 || dbg == 98 || dbg > k + 1 then
        if dbg == 97 then
          for t in stages[k]! do tacs := tacs.push (← `(tactic| ved_ss_timed $t))
        else tacs := tacs ++ stages[k]!
      if dbg == k + 2 then tacs := tacs.push stop
  let h0tacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro $insI hok),
    ← `(tactic| ved_ss_unfold [$exHelp,*] 0),
    ← `(tactic| ved_ss_core_simp_big [st0, $C:ident, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth, Signal.fst, Signal.snd, $exHelp,*]),
    ← `(tactic| all_goals decide +kernel)]
  let dbgS := ved.sseq.dbg.get (← getOptions)
  let stopT ← `(tactic| fail "stopped at debug stage")
  let skipT ← `(tactic| skip)
  let sa : TSyntax `tactic := if dbgS == 91 then stopT else skipT
  let sb : TSyntax `tactic := if dbgS == 92 then stopT else skipT
  let sc : TSyntax `tactic := if dbgS == 93 then stopT else skipT
  let sd : TSyntax `tactic := if dbgS == 94 then stopT else skipT
  `(by
      $sa
      have hord : OrderOk $M $B = true := (by decide +kernel)
      $sb
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$B, hord⟩, ?_⟩
      $sc
      apply outputs_of_order $B hord
      refine $oStep $C $M $B $f $O (by decide +kernel) ?R ?h0 ?hstep
      $sd
      case hstep =>
        $tacs*
      case h0 =>
        $h0tacs*)

/-- The leaves of the result tree: statement (bundled signal) and port names,
left-first.  `pre?` is the compiler's name prefix (`splitReturnLeaves`). -/
partial def bundleTree (ty e : Lean.Expr) (pre? : Option String) :
    MetaM (Lean.Expr × List String) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFn with
  | .const ``Sparkle.Core.Signal.Signal _ => pure (e, [pre?.getD "out"])
  | .const ``Prod _ =>
    let some (a, b) := (match ty.getAppArgs with | #[a, b] => some (a, b) | _ => none)
      | throwError "ved_struct%: malformed product {ty}"
    let p := pre?.getD "out"
    let (l, ln) ← bundleTree a (← mkAppM ``Prod.fst #[e]) (some (p ++ "_0"))
    let (r, rn) ← bundleTree b (← mkAppM ``Prod.snd #[e]) (some (p ++ "_1"))
    return (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, r], ln ++ rn)
  | .const ind _ =>
    let some (.inductInfo iv) := (← getEnv).find? ind
      | throwError "ved_struct%: {ty} is not a structure of signals"
    unless iv.ctors.length == 1 && !iv.isRec && iv.numIndices == 0 do
      throwError "ved_struct%: {ind} is not a single-constructor structure"
    let some sinfo := getStructureInfo? (← getEnv) ind
      | throwError "ved_struct%: {ind} is not a structure"
    if sinfo.fieldNames.isEmpty then throwError "ved_struct%: {ind} has no fields"
    -- fields, constructor order (the compiler's order: the ctor's binder names)
    let mut leaves : Array (Lean.Expr × List String) := #[]
    for f in sinfo.fieldNames do
      let pj ← mkProjection e f
      let fty ← inferType pj
      let nm := match pre? with | none => f.toString | some p => p ++ "_" ++ f.toString
      leaves := leaves.push (← bundleTree fty pj (some nm))
    -- right-nested pairs: f₁, (f₂, (… fₙ))
    let mut acc := leaves.back!
    for i in (List.range (leaves.size - 1)).reverse do
      let (l, ln) := leaves[i]!
      acc := (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, acc.1], ln ++ acc.2)
    return acc
  | _ => throwError "ved_struct%: {ty} is not a signal, a product or a structure"

open Lean Meta in
/-- `fun xs => bundle2 …` over the declaration's own projections, with the port names: the statement
term and the output names of a result that is a `×` / structure of signals (`bundleTree`). -/
def bundledStmtT (stmt : Lean.Expr) : MetaM (Lean.Expr × List String) := do
  forallTelescopeReducing (← inferType stmt) fun xs res => do
    let (bt, ns) ← bundleTree res (mkAppN stmt xs) none
    return (← mkLambdaFVars xs bt, ns)


end Tools.VedU1StructSeq
