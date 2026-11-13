import Lean
import Tools.VedU1ScriptSeq
import Tools.VedU1Loop

/-!
# The per-statement multi-register script (`Tools.VedU1ScriptSeqGen`)

Generator of the proof script for a module of assignments and registers whose registers are the
state of `Signal.loop`s (`Tools/VedU1Loop.lean`), built on `Tools.VedU1ScriptSeq.step_seq`:

* the step of the module is obtained ONCE from `step_seq` (one environment `E`, one equation
  per assignment over that same `E`, the register updates as the pure list `nextsOf`), never by
  unfolding `stepModule` over the whole body;
* every assignment's equation is normalised on its own (`ved_seq_simp ... at hs_j`), with the
  widths it needs given as one kernel-decided fact per name, and the data-input range facts from
  the contract as one kernel-decided fact per input;
* the new value of each register is read by `applyNexts_nextsOf` and a kernel-decided `regOf`.

It is an UNTRUSTED script like the others: the kernel checks the result against
`U1Stmt`.  `Tools/VedU1Entry.lean` runs it as a first attempt and falls back to the flat
script when it fails.
-/

namespace Tools.VedU1ScriptSeq

theorem or_mod (a b w n : Nat) (hn : 2 ^ w = n) : a <<< w ||| b % n = a * n + b % n := by
  subst hn
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos w)), Nat.shiftLeft_eq]

open Lean Meta Simp in
/-- `toNat` of a concatenation whose result width was already folded to a literal (`BitVec 32`
rather than `BitVec (16 + 16)`, after `Nat.reduceAdd`): the library lemmas are indexed on `m + n`
and do not fire.  The step is `Tools.VedU1Lemmas.toNat_append'`, whose left side is the same term
up to the literal arithmetic `16 + 16 = 32`. -/
simproc_decl vedToNatAppend (BitVec.toNat _) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let a := e.getArg! 1
  unless a.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let x := a.getArg! 4
  let y := a.getArg! 5
  let tx ← whnfR (← inferType x)
  let ty ← whnfR (← inferType y)
  unless tx.isAppOf ``BitVec && ty.isAppOf ``BitVec do return .continue
  let pf ← mkAppM ``Tools.VedU1Lemmas.toNat_append' #[x, y]
  let rhs := (← inferType pf).appArg!
  return .visit { expr := rhs, proof? := some pf }

open Lean Meta Simp in
/-- `simp` does not look into the argument of a `Signal.loop`: rewriting the body of a loop (a
function of the whole circuit) makes proof terms with `funext` / `congr` over the whole body, a
term the kernel cannot check in reasonable memory; the loop is read at ONE cycle instead
(`ved_seq_next`), where only values are rewritten. -/
simproc_decl vedLoopFreeze (Sparkle.Core.Signal.Signal.loop _) := fun e => do
  return .done { expr := e }

open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
syntax (name := vedSeqSimp) "ved_seq_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
macro_rules
  | `(tactic| ved_seq_simp [$ex,*] $[$loc]?) =>
    `(tactic| simp [↓vedLoopFreeze, stmtEq, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go, widthOf,
        Signal.register, OTy.obs, PTy.obs, PTy.sig, mask, Tools.VedU1ScriptSeq.or_mod _ _ _ _ rfl,
        Nat.shiftRight_eq_div_pow, Tools.VedU1Lemmas.evalOp_not_lit, 
        Tools.VedU1Lemmas.compl_val,
        Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit,
        Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val,
        Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val,
        Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add,
        Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub,
        Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val,
        Tools.VedU1Lemmas.evalOp_eq_lit, Tools.VedU1Lemmas.evalOp_mul_lit, Tools.VedU1Lemmas.evalOp_shl_lit, Tools.VedU1Lemmas.evalOp_shr_lit, Tools.VedU1Lemmas.evalOp_lt_u_lit, Tools.VedU1Lemmas.evalOp_le_u_lit, Tools.VedU1Lemmas.evalOp_gt_u_lit, Tools.VedU1Lemmas.evalOp_ge_u_lit, Tools.VedU1Lemmas.evalOp_lt_s_lit, Tools.VedU1Lemmas.mul_val, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedU1Lemmas.append_def_sc, Tools.VedU1Lemmas.append_def_cs, Tools.VedU1Lemmas.evalOp_asr_lit, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.mask_emod, Tools.VedU1Lemmas.slt_eq, Tools.VedU1Lemmas.ult_eq, Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val, Tools.VedU1Lemmas.evalOp_not_raw, Tools.VedU1Lemmas.evalOp_and_raw, Tools.VedU1Lemmas.evalOp_or_raw, Tools.VedU1Lemmas.evalOp_xor_raw, Tools.VedU1Lemmas.evalOp_sub_raw, Tools.VedU1Lemmas.shl_val, Tools.VedU1Lemmas.shr_val, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.append_def, Tools.VedU1Lemmas.toNat_append', Sparkle.Core.Signal.Signal.map,
        Seq.seq, Signal.beq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, BitVec.toNat_append,
        BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat,
        List.lookup, Option.getD_some, Option.getD_none, -Nat.reduceAdd, $ex,*] $[$loc]?)

/- `ved_seq_simp` without `dsimp`: a `dsimp` step carries no proof (the kernel is left to check
the definitional equality), and for arithmetic on symbolic values with big literals the kernel
evaluates `Nat.mul` / `Nat.shiftLeft` by unary recursion on the literal: memory without bound. -/
open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
syntax (name := vedSeqSimpNd) "ved_seq_simp_nd " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
macro_rules
  | `(tactic| ved_seq_simp_nd [$ex,*] $[$loc]?) =>
    `(tactic| simp (config := { dsimp := false }) [↓vedLoopFreeze, -Nat.shiftLeft_zero, Tools.VedU1ScriptSeq.shl_zero', stmtEq, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go, widthOf,
        Signal.register, OTy.obs, PTy.obs, PTy.sig, mask, Tools.VedU1ScriptSeq.or_mod _ _ _ _ rfl,
        Nat.shiftRight_eq_div_pow, Tools.VedU1Lemmas.evalOp_not_lit, 
        Tools.VedU1Lemmas.compl_val,
        Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit,
        Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val,
        Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val,
        Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add,
        Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub,
        Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val,
        Tools.VedU1Lemmas.evalOp_eq_lit, Tools.VedU1Lemmas.evalOp_mul_lit, Tools.VedU1Lemmas.evalOp_shl_lit, Tools.VedU1Lemmas.evalOp_shr_lit, Tools.VedU1Lemmas.evalOp_lt_u_lit, Tools.VedU1Lemmas.evalOp_le_u_lit, Tools.VedU1Lemmas.evalOp_gt_u_lit, Tools.VedU1Lemmas.evalOp_ge_u_lit, Tools.VedU1Lemmas.evalOp_lt_s_lit, Tools.VedU1Lemmas.mul_val, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedU1Lemmas.append_def_sc, Tools.VedU1Lemmas.append_def_cs, Tools.VedU1Lemmas.evalOp_asr_lit, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.mask_emod, Tools.VedU1Lemmas.slt_eq, Tools.VedU1Lemmas.ult_eq, Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val, Tools.VedU1Lemmas.evalOp_not_raw, Tools.VedU1Lemmas.evalOp_and_raw, Tools.VedU1Lemmas.evalOp_or_raw, Tools.VedU1Lemmas.evalOp_xor_raw, Tools.VedU1Lemmas.evalOp_sub_raw, Tools.VedU1Lemmas.shl_val, Tools.VedU1Lemmas.shr_val, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.append_def, Tools.VedU1Lemmas.toNat_append', Sparkle.Core.Signal.Signal.map,
        Seq.seq, Signal.beq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, BitVec.toNat_append,
        BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat,
        List.lookup, Option.getD_some, Option.getD_none, -Nat.reduceAdd, $ex,*] $[$loc]?)

syntax (name := vedSeqWideSimp) "ved_seq_wide_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_seq_wide_simp [$ex,*] $[$loc]?) =>
    `(tactic| simp (config := { maxSteps := 4000000 }) [vedToNatAppend, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond, Sparkle.IR.Semantics.toSigned, Tools.VedU1Lemmas.or_hi_8, Tools.VedU1Lemmas.or_hi_16, Tools.VedU1Lemmas.or_hi_24, Tools.VedU1Lemmas.or_hi_32, Tools.VedU1Lemmas.or_hi_40, Tools.VedU1Lemmas.or_hi_48, Tools.VedU1Lemmas.or_hi_64, Tools.VedU1Lemmas.and_mod_r, Tools.VedU1Lemmas.and_mod_l, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.toInt_ofNat_toSigned, Tools.VedU1Lemmas.beq_ofNat, Tools.VedU1Lemmas.toNat_decide_ite, Tools.VedU1Lemmas.toNat_not_decide_ite, Tools.VedU1Lemmas.toNat_ite_true, Tools.VedU1Lemmas.ofNat_eq_iff, Tools.VedU1Lemmas.ule_decide, Tools.VedU1Lemmas.ult_decide, Tools.VedU1Lemmas.xor_one_one, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, apply_ite BitVec.toNat, -Nat.reduceAdd, $ex,*] $[$loc]?)

/-- The closing tactic of the loop path (a copy of `ved_loop_close` of `Tools/VedU1Entry.lean`,
which this file cannot import): `ved_seq_wide_simp`, then `omega`, else a case split on the remaining
`if`s, the `|||` with a numeral that the split exposed (`x >>> 1 ||| 128`) rewritten by `ved_or_lit`,
and `omega`.  A concatenation whose width was folded to a literal is read back by `vedToNatAppend`. -/
syntax (name := vedSeqLoopClose) "ved_seq_loop_close " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_seq_loop_close [$ex,*]) =>
    `(tactic| ((try ved_seq_wide_simp [$ex,*]) <;> (first | omega | ((repeat' (split <;> (try simp only [vedToNatAppend, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, eq_self, ↓reduceIte, Nat.reduceEqDiff, not_true_eq_false, if_true, if_false, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true, *]))) <;> (try simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq] at *) <;> (try simp only [vedToNatAppend, Tools.VedU1Lemmas.toNat_append', Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, Nat.reduceDiv, Tools.VedU1Lemmas.xor_one_one, not_true_eq_false, Nat.zero_and, Nat.and_zero, Nat.one_and_eq_mod_two, Nat.and_one_is_mod, Nat.zero_xor, Nat.xor_zero, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true] at *) <;> (try ved_or_lit) <;> (try simp only [Nat.or_zero, Nat.zero_or]) <;> (try ved_bits_facts) <;> omega))))


/-! ## Loop-state variables with their defining equations -/

open Lean Meta Elab Tactic in
/-- `ved_seq_gen s`: like `Tools.VedU1Loop`'s `ved_loop_gen`, but every `(Signal.loop F).val s` found
in the goal or hypotheses is generalised to a variable `ved_Xj` KEEPING the equation `ved_hLj`
(`(Signal.loop F).val s = ved_Xj`), and the tuple is taken apart (`Bool` components stay variables:
`ved_seq_bools` splits them later).  The equation lets a later goal that mentions the same state
(after the loop is unfolded at `s + 1`) be rewritten to the same variables by `ved_seq_sub`. -/
elab "ved_seq_gen " s:ident : tactic => withMainContext do
  let sE ← elabTerm s.raw none
  let g ← getMainGoal
  let mut tgt ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  let loops := Tools.VedU1Loop.loopsOf tgt
  if loops.isEmpty then throwError "ved_seq_gen: no Signal.loop in the goal"
  for j in [0:loops.size] do
    let v ← mkAppM ``Sparkle.Core.Signal.Signal.val #[loops[j]!, sE]
    let vs ← Term.exprToSyntax v
    let X := mkIdent (Name.mkSimple s!"ved_X{j}")
    let hL := mkIdent (Name.mkSimple s!"ved_hL{j}")
    evalTactic (← `(tactic| generalize $hL:ident : $vs = $X:ident at *))
    let some α := loops[j]!.getAppArgs[1]? | throwError "ved_seq_gen: malformed Signal.loop"
    let n := (← Tools.VedU1Loop.stateComps α).length
    -- the state stays ONE variable: its components are read by projections (`rcases` on the
    -- tuple would put every later comparison of the state to the kernel as a `casesOn` motive)
    for i in [0:n] do
      let (pS, isB, isV) ← withMainContext do
        let some dX := (← getLCtx).findFromUserName? X.getId | throwError "ved_seq_gen: no state variable"
        let proj ← Tools.VedU1Loop.compProj dX.toExpr i
        let ty ← whnfR (← inferType proj)
        pure (← Term.exprToSyntax proj, ty.isConstOf ``Bool, ty.isAppOf ``BitVec)
      if isB then
        evalTactic (← `(tactic| have $(mkIdent (Name.mkSimple s!"ved_b{j}_{i}")):ident := Bool.toNat_le $pS))
      else if isV then
        evalTactic (← `(tactic| have $(mkIdent (Name.mkSimple s!"ved_v{j}_{i}")):ident := BitVec.isLt $pS))

open Lean Meta Elab Tactic in
/-- `ved_seq_sub` (`at h`): rewrite by every loop-state equation in the context: `ved_hLj` (the
state at `s` as the variables) and `ved_hUj` (the state at `s + 1`, already read off the body). -/
syntax (name := vedSeqSub) "ved_seq_sub" (" at " ident)? : tactic

open Lean Meta Elab Tactic in
@[tactic vedSeqSub] def evalVedSeqSub : Tactic := fun stx => withMainContext do
  let mut ids : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  let at? : Option Ident := if stx[1].isNone then none else some ⟨stx[1][1]⟩
  for d in ← getLCtx do
    let n := d.userName.toString
    if n.startsWith "ved_hL" || (at?.isNone && n.startsWith "ved_hU") then
      ids := ids.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):ident))
  unless ids.isEmpty do
    match at? with
    | some h => evalTactic (← `(tactic| simp only [$ids,*, -Nat.reduceAdd] at $h:ident))
    | none => evalTactic (← `(tactic| simp only [$ids,*, -Nat.reduceAdd]))

open Lean Meta Elab Tactic in
/-- `ved_seq_next s [ex]`: for every loop in the context, read its state at `s + 1` off the body
ONCE (`ved_hUj : (loop F).val (s+1) = …` in the variables of `ved_seq_gen`), so that no goal has
to carry the loop body: a goal that did made every rewriting step of the proof as big as the
loop, and the kernel check of the finished proof never returned. -/
syntax (name := vedSeqNext) "ved_seq_next " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

open Lean Meta Elab Tactic in
/-- `ved_seq_aux h (tacs)`: run `tacs` (which rewrite the hypothesis `h` in place) in a SUB-GOAL, and
put the resulting hypothesis back as an application of an auxiliary theorem (`mkAuxTheorem`).
A `have` whose value mentions earlier ones is substituted (`instantiateMVars` beta-reduces it) at
every use, and the copies are no longer shared once they sit under different numbers of binders:
the finished proof was a tree of 10^10 nodes that the kernel could not check.  As an auxiliary
theorem each derivation is kernel-checked once, and the proof refers to it by a constant. -/
syntax (name := vedSeqAux) "ved_seq_aux " ident " (" tacticSeq ")" : tactic

open Lean Meta Elab Tactic in
@[tactic vedSeqAux] def evalVedSeqAux : Tactic := fun stx => do
  let h : Ident := ⟨stx[1]⟩
  let tacs := stx[3]
  let aux ← withMainContext do
    let ty ← mkFreshTypeMVar
    let mv ← mkFreshExprMVar (some ty)
    let saved ← getGoals
    setGoals [mv.mvarId!]
    evalTactic tacs
    evalTactic (← `(tactic| exact $h))
    setGoals saved
    let val ← instantiateMVars mv
    let T1 ← instantiateMVars ty
    mkAuxTheorem T1 val (zetaDelta := true)
  let auxS ← Term.exprToSyntax aux
  evalTactic (← `(tactic| have $h:ident := $auxS))

open Lean Meta Elab Tactic in
/-- read every loop of the context and of the goal at the cycle `tm` (an `Expr`, or syntax) -/
def seqNextAt (tm : Term) (ex : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",") : TacticM Unit :=
  withMainContext do
  let mut tgt : Expr := mkConst ``True
  for d in ← getLCtx do
    unless d.isImplementationDetail do tgt := mkApp tgt (← instantiateMVars d.type)
  tgt := mkApp tgt (← instantiateMVars (← getMainTarget))
  let loops := Tools.VedU1Loop.loopsOf tgt
  for j in [0:loops.size] do
    let L := loops[j]!
    let args := L.getAppArgs
    unless args.size == 4 do throwError "ved_seq_next: malformed Signal.loop"
    let dom ← Term.exprToSyntax args[0]!
    let α ← Term.exprToSyntax args[1]!
    let inst ← Term.exprToSyntax args[2]!
    let F ← Term.exprToSyntax args[3]!
    let hU := mkIdent (Name.mkSimple s!"ved_hU{j}")
    let hL ← `(Lean.Parser.Tactic.simpLemma| h)
    let exh : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," :=
      Syntax.TSepArray.ofElems (#[hL] ++ ex.getElems)
    evalTactic (← `(tactic| have $hU:ident := @Tools.VedU1Loop.loop_val_unfold $dom $α $inst $F
        (fun _ _ => rfl) (fun s1 s2 t h => by ved_seq_simp [$exh,*]) $tm))
    evalTactic (← `(tactic| ved_seq_aux $hU:ident (
      try dsimp only [$ex,*, Sparkle.Core.Signal.Signal.map, Signal.register, Signal.beq, Signal.seq, Signal.ap,
        Sparkle.Core.Signal.bundle2, Functor.map, Seq.seq, Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le,
        OTy.obs, PTy.obs, PTy.sig, -Nat.reduceAdd] at $hU:ident
      ved_seq_simp [$ex,*] at $hU:ident
      ved_seq_sub at $hU:ident)))

open Lean Meta Elab Tactic in
@[tactic vedSeqNext] def evalVedSeqNext : Tactic := fun stx => do
  let sI : Ident := ⟨stx[1]⟩
  let sE ← `(term| $sI + 1)
  seqNextAt sE ⟨stx[3].getArgs⟩

/-- `ved_seq_next0 [ex]`: the same at cycle 0 (the initial value). -/
syntax (name := vedSeqNext0) "ved_seq_next0 " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic vedSeqNext0] def evalVedSeqNext0 : Tactic := fun stx => do
  seqNextAt (← `(term| 0)) ⟨stx[2].getArgs⟩

open Lean Meta Elab Tactic in
/-- `ved_seq_bools`: drop the hypotheses the rewriting is done with (the loop-state equations, the
per-statement equations, the seed facts: nothing reads them any more and `cases` would revert and
re-introduce every one that mentions the variable), then split every `Bool` loop-state variable
`ved_x…` (all goals). -/
elab "ved_seq_bools" : tactic => do
  if (← getGoals).isEmpty then return
  let drop ← withMainContext do
    let mut out : Array FVarId := #[]
    for d in ← getLCtx do
      let n := d.userName.toString
      if d.isImplementationDetail then continue
      let mentionsIR := (← instantiateMVars d.type).find? fun e =>
        e.isConst && (e.constName!.toString.startsWith "Sparkle.IR" || e.constName!.toString.startsWith "Tools.VedU1")
      if n.startsWith "ved_hL" || n.startsWith "ved_hU" || n.startsWith "hv" || n.startsWith "hs" || n.startsWith "hEr" || n.startsWith "hEin"
          || n.startsWith "hreg" || n.startsWith "hrg" || n.startsWith "hw" || n == "hfr" || n == "hall"
          || n == "hstep" || (mentionsIR.isSome && (← isProp d.type)) then
        out := out.push d.fvarId
    pure out
  -- later declarations first (they may depend on earlier ones)
  for fv in drop.reverse do
    let g ← getMainGoal
    try
      let g' ← g.clear fv
      replaceMainGoal [g']
    catch _ => pure ()
  let bs ← withMainContext do
    let mut bs : Array Expr := #[]
    for d in ← getLCtx do
      if d.userName.toString.startsWith "ved_b" then
        let t ← instantiateMVars d.type
        -- `Bool.toNat e ≤ 1`
        let a := t.getArg! 2
        if a.isAppOfArity ``Bool.toNat 1 then bs := bs.push (a.getArg! 0)
    pure bs
  for e in bs do
    let eS ← Term.exprToSyntax e
    evalTactic (← `(tactic| all_goals (try cases hbool : $eS)))

/-! ## Reading a field back out of a packed word

A `Signal.loop` over several registers is packed by the synthesizer into ONE wire
(`f % 2^w * 2^o + rest % 2^o`, nested) and each register is sliced back out
(`(wire / 2^k) % 2^w`).  Substituted into later statements the packed word makes every use a
copy of the whole chain, and `omega` cannot close the nested `%` / `/` chains.  `ved_seq_unpack at h`
rewrites, in a hypothesis `h`, every maximal `a % m` / `a / m` / `a / c % m` over Nat whose value
is one of the `toNat` atoms inside it: candidates are screened by evaluating both sides on
pseudo-random values of the atoms (cheap), then the equation is proved by `omega` and `h` is
rewritten with it.  UNTRUSTED like every tactic of the script: the kernel checks the proof. -/

section Unpack
open Lean Meta Elab Tactic

/-- value of a Nat arithmetic term under an assignment of its `toNat` atoms -/
partial def natEval (σ : Array (Expr × Nat)) (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do return (← natEval σ a) + (← natEval σ b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do return (← natEval σ a) * (← natEval σ b)
  | (``HMod.hMod, #[_, _, _, _, a, b]) => do
    let y ← natEval σ b
    return (← natEval σ a) % y
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
    let y ← natEval σ b
    return (← natEval σ a) / y
  | (``HPow.hPow, #[_, _, _, _, a, b]) => do
    let y ← natEval σ b
    if y > 4096 then none else return (← natEval σ a) ^ y
  | (``BitVec.toNat, _) => (σ.find? (·.1 == e)).map (·.2)
  | (``Bool.toNat, _) => (σ.find? (·.1 == e)).map (·.2)
  | _ => e.nat?

/-- the `toNat` atoms of `e` with their bit width -/
partial def toNatAtoms (e : Expr) (acc : Array (Expr × Nat)) : MetaM (Array (Expr × Nat)) := do
  if e.isAppOfArity ``BitVec.toNat 2 then
    let some w := (← instantiateMVars (e.getArg! 0)).nat? | return acc
    return if acc.any (·.1 == e) then acc else acc.push (e, w)
  if e.isAppOfArity ``Bool.toNat 1 then
    return if acc.any (·.1 == e) then acc else acc.push (e, 1)
  match e with
  | .app f a => do toNatAtoms a (← toNatAtoms f acc)
  | _ => return acc

/-- the Nat subterms `a % m`, `a / m` of `e` (outermost first) -/
partial def modDivs (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if (e.isAppOfArity ``HMod.hMod 6 || e.isAppOfArity ``HDiv.hDiv 6) && (e.getArg! 0).isConstOf ``Nat
    then acc.push e else acc
  match e with
  | .app f a => modDivs a (modDivs f acc)
  | _ => acc

/-- sample assignments: LCG over the atoms, values below `2^width` -/
def samples (atoms : Array (Expr × Nat)) (k : Nat) : Array (Array (Expr × Nat)) := Id.run do
  let mut out := #[]
  let mut seed := 0x9E3779B97F4A7C15 + 7919 * k
  for i in [0:k] do
    let mut row := #[]
    for (a, w) in atoms do
      seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let s2 := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let big := seed * 18446744073709551616 + s2
      let v := if i == 0 then 0 else if i == 1 then 2 ^ w - 1 else big % 2 ^ w
      row := row.push (a, v)
    out := out.push row
  return out

/-- a proof of `prop` by `omega` in a context holding ONLY the variables `prop` mentions (the
hypotheses of the script are many and big, and `omega` would read all of them); `Bool` atoms get
their `toNat ≤ 1` fact.  `none` when `omega` fails. -/
def omegaIn? (prop : Expr) (bools : Array Expr) : TacticM (Option Expr) := do
  let fvs := (Lean.collectFVars {} prop).fvarIds
  let mut lctx' : LocalContext := {}
  for d in ← getLCtx do
    if !d.isImplementationDetail && fvs.contains d.fvarId then lctx' := lctx'.addDecl d
  let m ← withLCtx lctx' (← getLocalInstances) (mkFreshExprMVar prop)
  let saved ← getGoals
  setGoals [m.mvarId!]
  let r ← try
      withMainContext do
        for b in bools do
          let h ← mkAppM ``Bool.toNat_le #[b.getArg! 0]
          evalTactic (← `(tactic| have := $(← Term.exprToSyntax h)))
        Tactic.withoutRecover (evalTactic (← `(tactic| omega)))
      pure (← getGoals).isEmpty
    catch _ => pure false
  setGoals saved
  if r then return some (← instantiateMVars m) else return none

elab "ved_seq_unpack " "at " h:ident : tactic => withMainContext do
  let some d0 := (← getLCtx).findFromUserName? h.getId | return
  let mut cur : FVarId := d0.fvarId
  for _ in [0:64] do
   let nxt ← withMainContext do
    let d ← cur.getDecl
    let ty ← instantiateMVars d.type
    let cands := (modDivs ty #[]).qsort (fun a b => a.approxDepth > b.approxDepth)
    let mut res : Option FVarId := none
    for t in cands do
      if t.hasLooseBVars then continue
      let atoms ← toNatAtoms t #[]
      if atoms.size < 2 then continue
      let rows := samples atoms 8
      for (c, _) in atoms do
        let ok := rows.all fun σ => match natEval σ t, natEval σ c with
          | some x, some y => x == y
          | _, _ => false
        unless ok do continue
        let some pf ← omegaIn? (← mkEq t c) (atoms.filterMap fun (a, w) => if w == 1 && a.isAppOfArity ``Bool.toNat 1 then some a else none) | continue
        let motive ← withLocalDeclD `z (mkConst ``Nat) fun z =>
          mkLambdaFVars #[z] (ty.replace fun x => if x == t then some z else none)
        let newH ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[motive, pf], d.toExpr]
        let g ← getMainGoal
        let g1 ← g.assert d.userName (← inferType newH) newH
        let (nv, g2) ← g1.intro1P
        let g3 ← g2.clear cur
        replaceMainGoal [g3]
        res := some nv
        break
      if res.isSome then break
    pure res
   match nxt with
   | some nv => cur := nv
   | none => return
end Unpack

open Lean Meta Elab Tactic in
/-- the `save_info` annotations the elaborator leaves in a goal hide a term from `omega` (it takes
`[mdata] a % 8` for an atom): remove the metadata from the target of every goal. -/
elab "ved_seq_unmdata" : tactic => do
  let gs ← getGoals
  let mut out : Array MVarId := #[]
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let t' ← Core.transform t (post := fun x => pure (if x.isMData then .done x.consumeMData else .done x))
    if t' == t then out := out.push g else out := out.push (← g.replaceTargetDefEq t')
  setGoals out.toList

open Lean Meta Elab Tactic in
/-- `ved_seq_close_each`: the closing tactic on every goal in turn; a goal it cannot close is an
error (the whole attempt is abandoned at once, the fallback script then runs). -/
elab "ved_seq_close_each" : tactic => do
  let gs ← getGoals
  for g in gs do
    setGoals [g]
    evalTactic (← `(tactic| ved_seq_unmdata))
    Tactic.withoutRecover
      (evalTactic (← `(tactic| ved_seq_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod, Int.bmod_def, BitVec.toNat_append, BitVec.toNat_ofNat, Tools.VedU1ScriptSeq.or_mod _ _ _ _ rfl])))
  setGoals []

/-! ## The generator -/

open Lean Elab Term Sparkle.IR.AST Sparkle.IR.Reorder Tools.VedU1Contract

/-- Names a statement mentions (reads, register outputs and inputs). -/
def stmtNames : Stmt → List String
  | .assign _ r => refsOf r
  | .register o _ (rst, _) e _ => o :: rst :: refsOf e
  | _ => []

private def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The script, or `none` when the module is outside its shape (a register whose input is not a
plain wire, a data input that is not scalar, no clock/reset for the registers).
`C M O B` are the checker's constants (contract, module, outputs, body), `F`/`nDom` the
declaration, `b0` the arrangement stored as `B`, `regs` the registers `(name, width)`. -/
def seqLoopScript (C M O B F : Name) (nDom : Nat) (m : Sparkle.IR.AST.Module) (b0 : List Stmt)
    (clkRst : Option (String × String)) (dataPorts : List Port) (regs : List (String × Nat))
    (helpers : Array Name) : TermElabM (Option Syntax) := do
  let some (clkN, rstN) := clkRst | return none
  -- registers: their input must be a plain wire, their reset the module's, their init non-negative
  let mut regInfo : Array (String × Nat × String × String × Int) := #[]
  for (r, w) in regs do
    match b0.find? (fun s => match s with | .register o .. => o == r | _ => false) with
    | some (.register _ _ (rst, _) (.ref wire) init) =>
      if rst != rstN || init < 0 then return none
      regInfo := regInfo.push (r, w, rst, wire, init)
    | _ => return none
  let fI := mkCIdent F
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  let Ci := mkCIdent C
  let Mi := mkCIdent M
  let Oi := mkCIdent O
  let Bi := mkCIdent B
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let hR := mkIdent `hR
  let vI := mkIdent `vsrc
  let hv := mkIdent `hvsrc
  let k := regs.length
  let hregs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hreg{i}")
  let rNames := (regs.map fun r => Syntax.mkStrLit r.1).toArray
  let rWidths := (regs.map fun r => Syntax.mkNumLit (toString r.2)).toArray
  -- widths of every name the body mentions
  let names := dedup (b0.flatMap stmtNames ++ dataPorts.map (·.name) ++ [rstN])
  let hws := (List.range names.length).toArray.map fun i => mkIdent (Name.mkSimple s!"hw{i}")
  let mut pre : Array (TSyntax `tactic) := #[]
  for (n, h) in names.zip hws.toList do
    let w := declWidth m n
    pre := pre.push (← `(tactic| have $h:ident : declWidth $Mi $(Syntax.mkStrLit n) = $(Syntax.mkNumLit (toString w)) := by decide +kernel))
  -- data inputs: the range facts, one per input
  let hins := (List.range dataPorts.length).toArray.map fun i => mkIdent (Name.mkSimple s!"hin{i}")
  for (i, p, h) in (List.range dataPorts.length).zip (dataPorts.zip hins.toList) |>.map fun (i, (p, h)) => (i, p, h) do
    let pn := Syntax.mkStrLit p.name
    let hwI := hws[(names.findIdx? (· == p.name)).getD 0]!
    match p.ty with
    | .bit | .bitVector _ => pure ()
    | _ => return none
    let wn := declWidth m p.name
    let iL := Syntax.mkNumLit (toString i)
    pre := pre.push (← `(tactic| have $h:ident : $insI $sI $pn < 2 ^ $(Syntax.mkNumLit (toString wn)) := by
        have h0 := Tools.VedU1ScriptSeq.inputsOk_nth $Ci $Mi $insI hok $sI $iL $pn (by decide +kernel)
        rw [$hwI:ident] at h0
        exact h0))
  -- the reset is held 0
  let hrst := mkIdent `hrst0
  pre := pre.push (← `(tactic| have $hrst:ident : $insI $sI $(Syntax.mkStrLit rstN) = 0 :=
    hok.2 $sI ($(Syntax.mkStrLit clkN), $(Syntax.mkStrLit rstN)) (by decide +kernel)))
  -- the environment E: inputs from the stream, registers from the state
  let hEin := (List.range dataPorts.length).toArray.map fun i => mkIdent (Name.mkSimple s!"hEin{i}")
  let mut postStep : Array (TSyntax `tactic) := #[]
  for (p, h) in dataPorts.zip hEin.toList do
    let pn := Syntax.mkStrLit p.name
    postStep := postStep.push (← `(tactic| have $h:ident : E $pn = $insI $sI $pn :=
      (hfr $pn (by decide +kernel)).trans
        (Tools.VedU1ScriptSeq.seedIn_input $Mi $insI $sI st $pn (by decide +kernel))))
  let hErst := mkIdent `hErst
  postStep := postStep.push (← `(tactic| have $hErst:ident : E $(Syntax.mkStrLit rstN) = 0 :=
    (hfr $(Syntax.mkStrLit rstN) (by decide +kernel)).trans
      ((Tools.VedU1ScriptSeq.seedIn_input $Mi $insI $sI st $(Syntax.mkStrLit rstN) (by decide +kernel)).trans $hrst)))
  let hEr := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hEr{i}")
  for i in [0:k] do
    let rn := rNames[i]!
    postStep := postStep.push (← `(tactic| have $(hEr[i]!):ident : E $rn = st $rn :=
      (hfr $rn (by decide +kernel)).trans
        (Tools.VedU1ScriptSeq.seedIn_state $Mi $insI $sI st $rn (by decide +kernel))))
    postStep := postStep.push (← `(tactic| rw [$(hregs[i]!):ident] at $(hEr[i]!):ident))
  -- register next values
  let hrgs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"hrg{i}")
  for i in [0:k] do
    let (r, _, rst, wire, init) := regInfo[i]!
    postStep := postStep.push (← `(tactic| have $(hrgs[i]!):ident :
      Tools.VedU1ScriptSeq.regOf $Bi $(Syntax.mkStrLit r) =
        some ($(Syntax.mkStrLit rst), Sparkle.IR.AST.Expr.ref $(Syntax.mkStrLit wire),
          ($(Syntax.mkNumLit (toString init.toNat)) : Int)) := rfl))
  -- one equation per assignment
  let nS := b0.length
  let hss := (List.range nS).toArray.map fun i => mkIdent (Name.mkSimple s!"hs{i}")
  let mut pats : Array (TSyntax `Lean.Parser.Tactic.rcasesPatLo) := #[]
  let mut assignIdx : Array Nat := #[]
  for i in [0:nS] do
    match b0[i]? with
    | some (.assign ..) =>
      pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| $(hss[i]!):ident))
      assignIdx := assignIdx.push i
    | _ => pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| _))
  pats := pats.push (← `(Lean.Parser.Tactic.rcasesPatLo| _))
  let allPat : TSyntax `rcasesPat ← `(rcasesPat| ⟨$[$pats],*⟩)
  let hwL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hws.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hEinL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hEin.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hErL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hEr.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hrgL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    hrgs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let hErstL ← `(Lean.Parser.Tactic.simpLemma| $hErst:ident)
  let mk (xs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :
      Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems xs
  -- the statements, in order, each on its own: the equations of the earlier statements are
  -- substituted (they are already small) and a packed word read back by `ved_seq_unpack`
  let hsL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (assignIdx.map fun i => hss[i]!).mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let mut perStmt : Array (TSyntax `tactic) := #[]
  for k in [0:assignIdx.size] do
    let i := assignIdx[k]!
    perStmt := perStmt.push (← `(tactic| ved_seq_aux $(hss[i]!):ident (
      ved_seq_simp_nd [$(mk (hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL.extract 0 k)),*] at $(hss[i]!):ident
      try ved_seq_unpack at $(hss[i]!):ident)))
  let applyL ← `(Lean.Parser.Tactic.simpLemma| Tools.VedU1ScriptSeq.applyNexts_nextsOf)
  let sigBase := #[← `(Lean.Parser.Tactic.simpLemma| srcOf), ← `(Lean.Parser.Tactic.simpLemma| $Ci:ident),
    ← `(Lean.Parser.Tactic.simpLemma| contractOf), ← `(Lean.Parser.Tactic.simpLemma| applyIns),
    ← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA
  let exReg := mk (#[applyL] ++ sigBase ++ hrgL ++ hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL)
  let closeTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| ved_seq_unmdata),
    ← `(tactic| all_goals (try simp only [vedToNatAppend, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq])),
    ← `(tactic| all_goals (try simp only [Nat.reduceAdd, Nat.reducePow])),
    ← `(tactic| all_goals (try simp (disch := first | ved_omega | decide) only [Nat.mod_mod_of_dvd])),
    ← `(tactic| all_goals (try ved_seq_wide_simp [BitVec.toNat_eq, Nat.and_one_is_mod, Int.bmod_def, Tools.VedU1Loop.ved_mul_lit_bv])),
    ← `(tactic| all_goals (try ved_bit_simp)),
    ← `(tactic| all_goals (try ved_or_lit)),
    ← `(tactic| all_goals (try ved_pack_simp)),
    ← `(tactic| all_goals (try ved_bits_facts)), ← `(tactic| all_goals (try ved_mul_facts)),
    ← `(tactic| all_goals (try ved_pack_simp)),
    ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])),
    ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat])),
    ← `(tactic| ved_seq_close_each)]
  let pats2 ← (hregs.toList).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  let hPat : TSyntax `rcasesPat ← match pats2 with
    | [] => `(rcasesPat| _)
    | _ => `(rcasesPat| ⟨$[$(pats2.toArray)],*⟩)
  let mut tacs : Array (TSyntax `tactic) := #[]
  tacs := tacs.push (← `(tactic| intro $insI hok $sI st mems $hR))
  tacs := tacs ++ pre
  let hv0 := mkIdent `hv0
  tacs := tacs.push (← `(tactic| obtain ⟨$vI, $hv0⟩ : ∃ v, v = srcOf $Ci $f $insI "out" $sI := ⟨_, rfl⟩))
  tacs := tacs.push (← `(tactic| have $hv := $hv0))
  tacs := tacs.push (← `(tactic| ved_seq_aux $hv:ident (
      try dsimp only [$Oi:ident, $Mi:ident, $Bi:ident, Tools.VedU1Contract.declWidth, srcOf, $Ci:ident, contractOf, applyIns, $fI:ident,
        Sparkle.Core.Signal.Signal.map, Signal.register, Signal.beq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, Functor.map, Seq.seq,
        Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le, OTy.obs, PTy.obs, PTy.sig, -Nat.reduceAdd, $(mk hsA),*] at $hv:ident
      ved_seq_simp [$Oi:ident, $Mi:ident, $Bi:ident, declWidth, srcOf, $Ci:ident, contractOf, applyIns, $fI:ident, $(mk hsA),*] at $hv:ident)))
  tacs := tacs.push (← `(tactic| ved_loop_R $insI [$rNames,*] $rWidths,*))
  tacs := tacs.push (← `(tactic| obtain $hPat := $hR))
  tacs := tacs.push (← `(tactic| ved_seq_gen $sI))
  tacs := tacs.push (← `(tactic| ved_seq_next $sI [$(mk (#[← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA)),*]))
  tacs := tacs.push (← `(tactic| obtain ⟨E, hstep, hfr, hall⟩ := Tools.VedU1ScriptSeq.step_seq (declWidth $Mi) mems $Bi
    (Tools.VedU1Contract.seedIn $Mi $insI $sI st) (by decide +kernel) (by decide +kernel)))
  tacs := tacs ++ postStep
  tacs := tacs.push (← `(tactic| obtain $allPat := hall))
  tacs := tacs ++ perStmt
  tacs := tacs.push (← `(tactic| refine ⟨E, Tools.VedU1ScriptSeq.nextsOf (declWidth $Mi) E $Bi, mems, hstep, ?_, ?_⟩))
  -- outputs
  let outTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro o ho),
    ← `(tactic| simp only [$Oi:ident, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho),
    ← `(tactic| subst ho),
    ← `(tactic| try dsimp only),
    ← `(tactic| rw [← $hv0:ident]),
    ← `(tactic| rw [$hv:ident]),
    ← `(tactic| simp only [$(mk hsL),*, -Nat.reduceAdd]),
    ← `(tactic| ved_seq_bools),
    ← `(tactic| all_goals try (repeat' apply And.intro))] ++ closeTacs
  let regTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| ved_seq_sub),
    ← `(tactic| ved_seq_simp [$exReg,*]),
    ← `(tactic| ved_seq_bools),
    ← `(tactic| all_goals try (repeat' apply And.intro))] ++ closeTacs
  let h0tacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro $insI hok),
    ← `(tactic| ved_seq_next0 [$(mk (#[← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA)),*]),
    ← `(tactic| ved_seq_sub),
    ← `(tactic| simp [Tools.VedU1Contract.st0, $Ci:ident, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.regsOf, $Mi:ident, Sparkle.IR.Semantics.encodeInit, Sparkle.IR.Semantics.mask, Tools.VedU1Contract.declWidth]),
    ← `(tactic| all_goals decide +kernel)]
  let oos := mkCIdent `Tools.VedU1Entry.outputs_of_step
  let b1 ← `(tactic| · $outTacs*)
  let b2 ← `(tactic| · $regTacs*)
  let hblock : Array (TSyntax `tactic) := tacs ++ #[b1, b2]
  let stx ← `(by
      have hord : OrderOk $Mi $Bi = true := by decide +kernel
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$Bi, hord⟩, ?_⟩
      apply Tools.VedU1Contract.outputs_of_order $Bi hord
      refine $oos $Ci $Mi $Bi $f $Oi (by decide +kernel) ?R ?h0 ?hstep
      case hstep =>
        $hblock*
      case h0 =>
        $h0tacs*)
  return some stx

end Tools.VedU1ScriptSeq
