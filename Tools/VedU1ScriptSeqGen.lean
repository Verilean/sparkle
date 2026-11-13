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

open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
syntax (name := vedSeqSimp) "ved_seq_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

open Sparkle.IR.Semantics Tools.VedU1Contract Sparkle.Core.Signal in
macro_rules
  | `(tactic| ved_seq_simp [$ex,*] $[$loc]?) =>
    `(tactic| simp [stmtEq, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go, widthOf,
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
    `(tactic| simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond, Sparkle.IR.Semantics.toSigned, Tools.VedU1Lemmas.or_hi_8, Tools.VedU1Lemmas.or_hi_16, Tools.VedU1Lemmas.or_hi_24, Tools.VedU1Lemmas.or_hi_32, Tools.VedU1Lemmas.or_hi_40, Tools.VedU1Lemmas.or_hi_48, Tools.VedU1Lemmas.or_hi_64, Tools.VedU1Lemmas.and_mod_r, Tools.VedU1Lemmas.and_mod_l, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.toInt_ofNat_toSigned, Tools.VedU1Lemmas.beq_ofNat, Tools.VedU1Lemmas.toNat_decide_ite, Tools.VedU1Lemmas.toNat_not_decide_ite, Tools.VedU1Lemmas.toNat_ite_true, Tools.VedU1Lemmas.ofNat_eq_iff, Tools.VedU1Lemmas.ule_decide, Tools.VedU1Lemmas.ult_decide, Tools.VedU1Lemmas.xor_one_one, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, apply_ite BitVec.toNat, -Nat.reduceAdd, $ex,*] $[$loc]?)

/-- The closing tactic of the wide path (`scriptFor`): `ved_seq_wide_simp`, then `omega`, else a
case split on the remaining `if`s and `omega`.  `ex` are extra simp lemmas (the range facts of
the wide inputs). -/
syntax (name := vedSeqWideClose) "ved_seq_wide_close " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_seq_wide_close [$ex,*]) =>
    `(tactic| ((try ved_seq_wide_simp [$ex,*]) <;> (first | omega | ((repeat' split) <;> (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, Nat.reduceDiv, Tools.VedU1Lemmas.xor_one_one, not_true_eq_false] at *) <;> omega))))

/-- `ved_seq_wide_close` for the loop path: after the case split, the `|||` with a numeral that the
split exposed (`x >>> 1 ||| 128`) is rewritten by `ved_or_lit` before `omega`. -/
syntax (name := vedSeqLoopClose) "ved_seq_loop_close " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ved_seq_loop_close [$ex,*]) =>
    `(tactic| ((try ved_seq_wide_simp [$ex,*]) <;> (first | omega | ((repeat' (split <;> (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, eq_self, ↓reduceIte, Nat.reduceEqDiff, not_true_eq_false, if_true, if_false, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true, *]))) <;> (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, Nat.reduceDiv, Tools.VedU1Lemmas.xor_one_one, not_true_eq_false, Nat.zero_and, Nat.and_zero, Nat.one_and_eq_mod_two, Nat.and_one_is_mod, Nat.zero_xor, Nat.xor_zero, true_and, and_true, false_and, and_false, or_false, false_or, or_true, true_or, not_false_eq_true] at *) <;> (try ved_or_lit) <;> (try simp only [Nat.or_zero, Nat.zero_or]) <;> (try ved_bits_facts) <;> omega))))


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
    let xs := (List.range (n + 1)).toArray.map fun i => mkIdent (Name.mkSimple s!"ved_x{j}_{i}")
    let pats ← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
    evalTactic (← `(tactic| rcases $X:ident with ⟨$pats,*⟩))

open Lean Meta Elab Tactic in
/-- `ved_seq_sub`: rewrite by every `ved_hLj` in the context (the loop states at `s`). -/
elab "ved_seq_sub" : tactic => withMainContext do
  let mut ids : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for d in ← getLCtx do
    if d.userName.toString.startsWith "ved_hL" then
      ids := ids.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):ident))
  unless ids.isEmpty do
    try evalTactic (← `(tactic| simp only [$ids,*]))
    catch e =>
      logInfo m!"ved_seq_sub failed at goal:\n{← getMainGoal}"
      throw e

open Lean Meta Elab Tactic in
/-- `ved_seq_bools`: split every `Bool` loop-state variable `ved_x…` (all goals). -/
elab "ved_seq_bools" : tactic => do
  let names ← withMainContext do
    let mut names : Array Name := #[]
    for d in ← getLCtx do
      if d.userName.toString.startsWith "ved_x" && (← whnfR d.type).isConstOf ``Bool then
        names := names.push d.userName
    pure names
  for n in names do
    evalTactic (← `(tactic| all_goals (try cases $(mkIdent n):ident)))

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
    (helpers : Array Name) (stop : Nat := 0) : TermElabM (Option Syntax) := do
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
  -- the statements, in order, each on its own
  let mut perStmt : Array (TSyntax `tactic) := #[]
  for i in assignIdx do
    perStmt := perStmt.push (← `(tactic| ved_seq_simp [$(mk (hwL ++ hEinL ++ hErL ++ #[hErstL])),*] at $(hss[i]!):ident))
  let hsL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (assignIdx.map fun i => hss[i]!).mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let applyL ← `(Lean.Parser.Tactic.simpLemma| Tools.VedU1ScriptSeq.applyNexts_nextsOf)
  let sigBase := #[← `(Lean.Parser.Tactic.simpLemma| srcOf), ← `(Lean.Parser.Tactic.simpLemma| $Ci:ident),
    ← `(Lean.Parser.Tactic.simpLemma| contractOf), ← `(Lean.Parser.Tactic.simpLemma| applyIns),
    ← `(Lean.Parser.Tactic.simpLemma| $fI:ident)] ++ hsA
  let exOut := mk (sigBase ++ hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL)
  let exReg := mk (#[applyL] ++ sigBase ++ hrgL ++ hwL ++ hEinL ++ hErL ++ #[hErstL] ++ hsL)
  let closeTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| all_goals (try ved_seq_wide_simp [BitVec.toNat_eq, Nat.and_one_is_mod, Tools.VedU1Loop.ved_mul_lit_bv])),
    ← `(tactic| all_goals (try ved_bit_simp)),
    ← `(tactic| all_goals (try ved_or_lit)),
    ← `(tactic| all_goals (try ved_pack_simp)),
    ← `(tactic| all_goals (try ved_bits_facts)), ← `(tactic| all_goals (try ved_mul_facts)),
    ← `(tactic| all_goals (try ved_pack_simp)),
    ← `(tactic| all_goals (try simp only [Nat.mod_mul_mod, Nat.mul_mod_mod])),
    ← `(tactic| all_goals (try simp only [Tools.VedU1Loop.ved_mul_lit_nat])),
    ← `(tactic| all_goals ved_seq_loop_close [BitVec.toNat_eq, Nat.and_one_is_mod])]
  let pats2 ← (hregs.toList).mapM fun h => `(Lean.Parser.Tactic.rcasesPatLo| $h:ident)
  let hPat : TSyntax `rcasesPat ← match pats2 with
    | [] => `(rcasesPat| _)
    | _ => `(rcasesPat| ⟨$[$(pats2.toArray)],*⟩)
  let mut tacs : Array (TSyntax `tactic) := #[]
  tacs := tacs.push (← `(tactic| intro $insI hok $sI st mems $hR))
  tacs := tacs ++ pre
  tacs := tacs.push (← `(tactic| obtain ⟨$vI, $hv⟩ : ∃ v, v = srcOf $Ci $f $insI "out" $sI := ⟨_, rfl⟩))
  tacs := tacs.push (← `(tactic| ved_seq_simp [$Oi:ident, $Mi:ident, $Bi:ident, declWidth, srcOf, $Ci:ident, contractOf, applyIns, $fI:ident, $(mk hsA),*] at $hv:ident))
  tacs := tacs.push (← `(tactic| ved_loop_R $insI [$rNames,*] $rWidths,*))
  tacs := tacs.push (← `(tactic| clear $hv))
  tacs := tacs.push (← `(tactic| obtain $hPat := $hR))
  tacs := tacs.push (← `(tactic| ved_seq_gen $sI))
  tacs := tacs.push (← `(tactic| obtain ⟨E, hstep, hfr, hall⟩ := Tools.VedU1ScriptSeq.step_seq (declWidth $Mi) mems $Bi
    (Tools.VedU1Contract.seedIn $Mi $insI $sI st) (by decide +kernel) (by decide +kernel)))
  let nA := tacs.size
  tacs := tacs ++ postStep
  let nB := tacs.size
  tacs := tacs.push (← `(tactic| obtain $allPat := hall))
  tacs := tacs ++ perStmt
  let nC := tacs.size
  tacs := tacs.push (← `(tactic| refine ⟨E, Tools.VedU1ScriptSeq.nextsOf (declWidth $Mi) E $Bi, mems, hstep, ?_, ?_⟩))
  -- outputs
  let outTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro o ho),
    ← `(tactic| simp only [$Oi:ident, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho),
    ← `(tactic| subst ho),
    ← `(tactic| try dsimp only),
    ← `(tactic| ved_seq_simp [$exOut,*]),
    ← `(tactic| ved_seq_sub),
    ← `(tactic| try ved_seq_simp [$exOut,*]),
    ← `(tactic| ved_seq_bools),
    ← `(tactic| all_goals try (repeat' apply And.intro))] ++ closeTacs
  let regTacs : Array (TSyntax `tactic) := #[
    ← `(tactic| ved_loop_unfold ($sI + 1)),
    ← `(tactic| ved_seq_simp [$exReg,*]),
    ← `(tactic| ved_seq_sub),
    ← `(tactic| try ved_seq_simp [$exReg,*]),
    ← `(tactic| ved_seq_bools),
    ← `(tactic| all_goals try (repeat' apply And.intro))] ++ closeTacs
  let h0tacs : Array (TSyntax `tactic) := #[
    ← `(tactic| intro $insI hok),
    ← `(tactic| ved_loop_unfold 0),
    ← `(tactic| simp [st0, $Ci:ident, contractOf, regsOf, $Mi:ident, encodeInit, mask, declWidth]),
    ← `(tactic| all_goals decide +kernel)]
  let oos := mkCIdent `Tools.VedU1Entry.outputs_of_step
  let stopT ← `(tactic| (trace_state; fail "seq stop"))
  let stop := if stop == 1 then nA else if stop == 2 then nB else if stop == 3 then nC else if stop == 4 then nC + 1 else stop
  let outTacs := if stop ≥ 10 && stop < 100 then (outTacs.extract 0 (stop - 10)).push stopT else outTacs
  let regTacs := if stop ≥ 100 then (regTacs.extract 0 (stop - 100)).push stopT else regTacs
  let stop := if stop ≥ 10 then 0 else stop
  if stop > 0 then tacs := (tacs.extract 0 stop).push stopT
  let stx ← `(by
      have hord : OrderOk $Mi $Bi = true := by decide +kernel
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$Bi, hord⟩, ?_⟩
      apply Tools.VedU1Contract.outputs_of_order $Bi hord
      refine $oos $Ci $Mi $Bi $f $Oi (by decide +kernel) ?R ?h0 ?hstep
      case hstep =>
        $tacs*
        · $outTacs*
        · $regTacs*
      case h0 =>
        $h0tacs*)
  return some stx

end Tools.VedU1ScriptSeq
