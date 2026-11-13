import Tools.VedU1Entry
import Tools.VedU1Packed
import Tools.VedU1MultiSeqLoop

/-!
# Packed result with registers (`Signal d (A × B)` whose body has `Signal.loop` registers)

Generated (untrusted) proof script for `PackedStmt C M f` when the module has registers
(docs/VED-U1-MULTISEQ.md).  The statement is the packed one (`Tools/VedU1Packed.lean`); the contract now
also carries the clock/reset names and the register initial values, which the packed
entry reads from the returned module exactly as `contractOf` does for the single-port entry.

The proof is the loop path's (`Tools.VedU1Entry.loopScriptFor`: the invariant "register `n`
of the module is the `toNat` of the loop-state component it implements", by induction on the
cycle) over the packed value `packedF tbl f`; `srcOf_packed` turns the module's port into
`OTy.packNat` of the declaration's own result, which the same simp set unfolds.
-/

namespace Tools.VedU1MultiSeq

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed Tools.VedU1Loop Tools.VedU1MultiSeqLoop
open Lean Meta Elab Term

/-- Debugging/controls only: stop the generated proof after stage `k` and print the goals. -/
register_option ved.multiseq.dbg : Nat := {
  defValue := 0
  descr := "ved.multiseq.dbg: stop the packed-with-registers script after stage k (0: off)"
}

/-- The generated (untrusted) script for `PackedStmt C M f`, `C`'s module having the registers
`regs` (name, width) of `Signal.loop`s. -/
def packedLoopScript (nm : Names) (F : Name) (nDom : Nat) (regs : List (String × Nat))
    (helpers : Array Name) : TermElabM Syntax := do
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let B := mkCIdent nm.body
  let fI := mkCIdent F
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
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
  tacs := tacs.push (← `(tactic| intro $insI hok $sI st mems $hR))
  tacs := tacs.push (← `(tactic| have $hinI := hok.1 $sI))
  tacs := tacs.push (← `(tactic| have $hrstI := hok.2 $sI))
  tacs := tacs.push (← `(tactic| simp [PContract.core, collapse, $C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at $hinI:ident $hrstI:ident))
  let keyI := mkIdent `key
  tacs := tacs.push (← `(tactic| have $keyI : ∀ t, srcOf (PContract.core $C) (packedF ($C).tbl $f) $insI "out" t =
      OTy.packNat ($C).tbl.out ((applyIns ($C).tbl.ins ($C).inNames $insI $f).val t) := fun t => srcOf_packed $C $f $insI t))
  tacs := tacs.push (← `(tactic| simp only [$O:ident, List.mem_singleton, forall_eq, $keyI:ident]))
  tacs := tacs.push (← `(tactic| obtain ⟨$vI, $hv⟩ : ∃ v, v = OTy.packNat ($C).tbl.out ((applyIns ($C).tbl.ins ($C).inNames $insI $f).val $sI) := ⟨_, rfl⟩))
  tacs := tacs.push (← `(tactic| ved_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, PContract.core, collapse, $C:ident, contractOf, applyIns, $fI:ident, Tools.VedU1MultiSeqLemmas.OTy_packNat_pair, Tools.VedU1MultiSeqLemmas.OTy_packNat_leaf, OTy.width, PTy.width, Signal.fst, Signal.snd, $exHelp,*] at $hv:ident))
  tacs := tacs.push (← `(tactic| ved_loop_R' $insI [$rNames,*] $rWidths,*))
  tacs := tacs.push (← `(tactic| clear $hv))
  tacs := tacs.push (← `(tactic| obtain $hPat := $hR))
  let closing ← if ved.multiseq.dbg.get (← getOptions) == 99
    then `(tactic| all_goals (first | ved_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod] | fail "ved_loop_close failed here"))
    else `(tactic| all_goals ved_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])
  let stages : Array (Array (TSyntax `tactic)) := #[
    #[← `(tactic| ved_loop_unfold' [$exHelp,*] ($sI + 1))],
    #[← `(tactic| ved_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, PContract.core, collapse, $C:ident, contractOf, applyIns, $fI:ident, Tools.VedU1MultiSeqLemmas.OTy_packNat_pair, Tools.VedU1MultiSeqLemmas.OTy_packNat_leaf, OTy.width, PTy.width, Signal.fst, Signal.snd, $ex1,*])],
    #[← `(tactic| ved_loop_gen' $sI)],
    #[← `(tactic| all_goals refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩),
      ← `(tactic| all_goals ved_core_simp_big [$O:ident, $M:ident, $B:ident, declWidth, srcOf, PContract.core, collapse, $C:ident, contractOf, applyIns, $fI:ident, Tools.VedU1MultiSeqLemmas.OTy_packNat_pair, Tools.VedU1MultiSeqLemmas.OTy_packNat_leaf, OTy.width, PTy.width, Signal.fst, Signal.snd, $ex2,*]),
      ← `(tactic| all_goals try (repeat' apply And.intro))],
    #[← `(tactic| all_goals (try ved_wide_simp [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_bv]))],
    #[← `(tactic| all_goals (try ved_bit_simp))],
    #[← `(tactic| all_goals (try ved_or_lit))],
    #[← `(tactic| all_goals (try ved_pack_simp))],
    #[← `(tactic| all_goals (try ved_bits_facts)), ← `(tactic| all_goals (try ved_mul_facts)),
      ← `(tactic| all_goals (try ved_pack_simp)),
      ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])),
      ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat]))],
    #[closing]]
  let dbg := ved.multiseq.dbg.get (← getOptions)
  if dbg == 50 then
    tacs := tacs.push (← `(tactic| ved_loop_unfold1 [$exHelp,*] ($sI + 1)))
  let stop ← `(tactic| (trace_state; fail "stopped at debug stage"))
  if dbg == 1 || (dbg ≥ 50 && dbg < 99) then tacs := tacs.push stop
  else
    for k in [0:stages.size] do
      if dbg == 0 || dbg > k + 1 then tacs := tacs ++ stages[k]!
      if dbg == k + 2 then tacs := tacs.push stop
  let h0tacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro $insI hok),
    ← `(tactic| ved_loop_unfold' [$exHelp,*] 0),
    ← `(tactic| ved_core_simp_big [st0, PContract.core, $C:ident, collapse, contractOf, regsOf, $M:ident, encodeInit, mask, declWidth, Signal.fst, Signal.snd, $exHelp,*]),
    ← `(tactic| all_goals decide +kernel)]
  `(by
      have hP : PackCover $C := by decide
      have hU : U1Stmt (PContract.core $C) $M (packedF ($C).tbl $f) := by
        have hord : OrderOk $M $B = true := by decide +kernel
        refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$B, hord⟩, ?_⟩
        apply outputs_of_order $B hord
        refine outputs_of_step (PContract.core $C) $M $B (packedF ($C).tbl $f) $O (by decide +kernel) ?R ?h0 ?hstep
        case hstep =>
          $tacs*
        case h0 =>
          $h0tacs*
      exact ⟨hP, hU, slices_of_outputs hP.1 hU.2.2.2.2⟩)

end Tools.VedU1MultiSeq
