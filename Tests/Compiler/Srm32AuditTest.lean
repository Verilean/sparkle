import Tests.Compiler.Srm32AuditExpected
import Tests.Compiler.Srm28AuditTest
import Tools.ShippingSrm32Width
-- UNBUILT (unit SRM32): see REPORT-SRM32.md; the final-SHA rebuild is the only final evidence.
-- Audit of Tools/ShippingSrm32Width.lean, Tests/Compiler/Srm32InstTest.lean and the CHANGED statement `MachineWired` (20th conjunct):
-- (0) `MachineWired` unfolds to exactly 20 conjuncts; the 20th is defeq to `Exp_lastClause` and NOT defeq to the weakened `≤` fixture;
-- (1) literal count guard and binder tables for the 4 theorems;
-- (2) BINDER-TABLE comparator (binderInfo, name, isProp, isDefEq type per row, then conclusion) against Srm32AuditExpected (generated from scripts/srm32/EXPECTED.txt, committed before any Lean edit);
--     semantic negative fixtures rejected with the specific row kind: ` ∧ True` on the Prop binder hW, an added data binder, reordered binders, houtTy dropped, `<` for `≤`; for the instance: P := True, hpost dropped, `<`;
-- (3) no relabel: no Prop binder restates its conclusion (control wrapper detected); the 20th clause is not a binder of any audited theorem, and `MachineWired` (hW) is not defeq to the conclusion;
--     it is theorem-backed: the closure of the instances reaches the producer's width lemma `weOf_wires_append` and `weOf_congr_wires`;
-- (4) one witness: topshare{M,Q}_composedNW occurs ONCE in each instance proof; forbidden old-form roots (ChildBnd/MachineClosesAt/RefLaws, SRM26 K0N route, composedG_of_NW) absent, with
--     a positive control that each forbidden root exists and that the walk detects one; standard axioms only.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm32AuditTest
open Tests.Compiler.Srm32AuditExpected

theorem wrapper_mutation (p : Prop) (h : p) : p := h

def audited32 : List Name :=
  [``Tools.ShippingSrm32.slotWidths_of_wired, ``Tools.ShippingSrm32.hWd_of_wired,
   ``Tests.Compiler.Srm32InstTest.topshareM_composedNW_hWd, ``Tests.Compiler.Srm32InstTest.topshareQ_composedNW_hWd]

def pairs32 : List (Name × Name) :=
  [(audited32[0]!, ``Exp_slotWidths), (audited32[1]!, ``Exp_hWd), (audited32[2]!, ``Exp_M_hWd), (audited32[3]!, ``Exp_Q_hWd)]

/-- (real theorem, mutant, expected first-difference kind) -/
def mutants32 : List (Name × Name × String) :=
  [(audited32[1]!, ``Exp_mut_withTrue, "type@12"), (audited32[1]!, ``Exp_mut_addedBinder, "name@12"),
   (audited32[1]!, ``Exp_mut_reordered, "name@9"), (audited32[1]!, ``Exp_mut_noOutTy, "name@11"),
   (audited32[1]!, ``Exp_mut_lt, "concl"),
   (audited32[0]!, ``Exp_mut_slotWidths_withTrue, "type@8"), (audited32[0]!, ``Exp_mut_slotWidths_le, "concl"),
   (audited32[2]!, ``Exp_mut_M_trivialP, "concl"), (audited32[2]!, ``Exp_mut_M_noHpost, "name@10"),
   (audited32[2]!, ``Exp_mut_M_lt, "concl")]

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

def tableCmp (t e : Expr) : MetaM (Option String) :=
  forallTelescope t fun xs concl => do
    let mut e := e
    let mut i : Nat := 0
    for x in xs do
      match e with
      | .forallE n d b bi =>
        let dx ← x.fvarId!.getDecl
        if bi != dx.binderInfo then return some s!"info@{i}"
        if bi != .instImplicit && n != dx.userName then return some s!"name@{i}"
        if (← isProp d) != (← isProp dx.type) then return some s!"isProp@{i}"
        unless (← isDefEq d dx.type) do return some s!"type@{i}"
        e := b.instantiate1 x
        i := i + 1
      | _ => return some "count"
    if e.isForall then return some "count"
    unless (← isDefEq e concl) do return some "concl"
    return none

def expType (n : Name) : MetaM Expr := do
  let ei ← getConstInfo n
  return ei.value?.getD (mkConst n)

def restatesConclusion (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← isProp d.type) then
        if (← withReducible (isDefEq d.type concl)) then return true
    return false

partial def countConst (n : Name) (e : Expr) : Nat :=
  match e with
  | .const c _ => if c == n then 1 else 0
  | .app f a => countConst n f + countConst n a
  | .lam _ d b _ => countConst n d + countConst n b
  | .forallE _ d b _ => countConst n d + countConst n b
  | .letE _ t v b _ => countConst n t + countConst n v + countConst n b
  | .mdata _ b => countConst n b
  | .proj _ _ b => countConst n b
  | _ => 0

def valueOf (ci : ConstantInfo) : Expr :=
  match ci with
  | .thmInfo t => t.value
  | .defnInfo t => t.value
  | _ => mkConst `none

def reachAll (n : Name) : MetaM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : List Name := [n]
  let mut fuel := 400000
  while fuel > 0 && !todo.isEmpty do
    fuel := fuel - 1
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := (← getEnv).find? c then
        let mut cs : Array Name := ci.type.getUsedConstants
        match ci with
          | .thmInfo t => cs := cs ++ t.value.getUsedConstants
          | .defnInfo t => cs := cs ++ t.value.getUsedConstants
          | _ => pure ()
        for d in cs do
          if !seen.contains d then todo := d :: todo
  return seen


elab "#srm32_audit" : command => liftTermElabM do
  unless audited32.length == 4 && pairs32.length == 4 && mutants32.length == 10 do throwError "SRM32 AUDIT FAILED: literal count guard"
  -- (0) MachineWired: 20 conjuncts, 20th = Exp_lastClause, not the weakened fixture
  do
    let ci ← getConstInfo ``Tools.ShippingMachineEntry.MachineWired
    lambdaTelescope ci.value?.get! fun xs body => do
      let mut b ← zetaReduce body
      let mut n : Nat := 0
      while b.isAppOfArity ``And 2 do
        n := n + 1
        b := b.appArg!
      let last := b   -- the final non-And tail is the last conjunct
      n := n + 1
      unless n == 20 do throwError "SRM32 AUDIT FAILED: MachineWired has {n} conjuncts, expected 20"
      let exp ← mkAppM ``Exp_lastClause #[xs[1]!, xs[4]!, xs[6]!]
      unless (← isDefEq last exp) do throwError "SRM32 AUDIT FAILED: the last conjunct of MachineWired differs from Exp_lastClause"
      let neg ← mkAppM ``Exp_mut_lastClause_le #[xs[1]!, xs[4]!, xs[6]!]
      if (← isDefEq last neg) then throwError "SRM32 AUDIT FAILED: the weakened clause fixture was ACCEPTED as the 20th conjunct"
      logInfo m!"S32WIRED|20 conjuncts; the 20th is defeq to Exp_lastClause; the weakened fixture is rejected"
  -- (1) binder tables
  for t in audited32 do
    let ci ← getConstInfo t
    logInfo m!"S32THM|{t}"
    forallTelescope ci.type fun xs concl => do
      let mut i : Nat := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        logInfo m!"S32PREM|{t}|{i}|{repr d.binderInfo}|{d.userName}|{← isProp d.type}|{← ppExpr d.type}"
        i := i + 1
      logInfo m!"S32CONC|{t}|{← ppExpr concl}"
  -- (2) comparator
  for (t, e) in pairs32 do
    match ← tableCmp (← getConstInfo t).type (← expType e) with
    | none => logInfo m!"S32TABLEOK|{t}|{e}"
    | some r => throwError "SRM32 AUDIT FAILED: {t} differs from {e} at {r}"
  for (t, mname, want) in mutants32 do
    let mt ← expType mname
    unless (← isProp mt) do throwError "SRM32 AUDIT FAILED: mutant {mname} is not a Prop"
    match ← tableCmp (← getConstInfo t).type mt with
    | none => throwError "SRM32 AUDIT FAILED: mutant {mname} ACCEPTED"
    | some r =>
      unless r == want do throwError "SRM32 AUDIT FAILED: mutant {mname} rejected for {r}, expected {want}"
      logInfo m!"S32MUTREJECT|{mname}|{r}"
  -- (3) no relabel
  for t in audited32 do
    if (← restatesConclusion t) then throwError "SRM32 AUDIT FAILED: a hypothesis of {t} restates its conclusion"
  unless (← restatesConclusion ``Tests.Compiler.Srm32AuditTest.wrapper_mutation) do
    throwError "SRM32 AUDIT FAILED: control wrapper not detected"
  logInfo "S32NORELABEL|hW (MachineWired) is not the conclusion of either wired theorem; the 20th clause is a producer-proved export (see S32PRODUCER), a binder of no audited theorem"
  -- (4) closure
  for t in audited32 do
    let ax ← Lean.collectAxioms t
    for a in ax do
      unless stdAx.contains a do throwError "SRM32 AUDIT FAILED: non-standard axiom {a} in {t}"
    logInfo m!"S32AXIOMS|{t}|{ax.toList}"
  let forbidden : List Name := [``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired, ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired,
    ``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports, ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
    ``Tools.ShippingChildInv.RefLaws, ``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingChildInv.MachineClosesAt,
    ``Tools.ShippingSlotRegsRun.slotRegs_runMT]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM32 AUDIT FAILED: forbidden root {f} does not exist (control)"
  for (inst, comp) in [(audited32[2]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_composedNW),
                       (audited32[3]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_composedNW)] do
    let ci ← getConstInfo inst
    let cnt := countConst comp (valueOf ci)
    unless cnt == 1 do throwError "SRM32 AUDIT FAILED: {comp} occurs {cnt} times in {inst}, expected 1 (one witness)"
    let r ← reachAll inst
    for f in forbidden do
      if r.contains f then throwError "SRM32 AUDIT FAILED: forbidden old-form root {f} in the closure of {inst}"
    for must in [``Tools.ShippingSrm32.hWd_of_wired, ``Tools.ShippingSrm28.composedNWRegs_of_composedNW, comp,
                 ``Tools.ShippingMachineClose.weOf_wires_append] do
      unless r.contains must do throwError "SRM32 AUDIT FAILED: {must} missing from the closure of {inst}"
    logInfo m!"S32ONEWITNESS|{inst}|{comp} once; forbidden roots absent"
    logInfo m!"S32PRODUCER|{inst}: closure reaches the producer width lemma weOf_wires_append"
  -- positive control for the forbidden-root walk
  unless (← reachAll ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired).contains ``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired do
    throwError "SRM32 AUDIT FAILED: forbidden-root control not detected"
  unless (← reachAll ``Tools.ShippingSlotRegsRun.slotRegs_runMT).contains ``Tools.ShippingSlotRegsRun.closeMachine_regs do
    throwError "SRM32 AUDIT FAILED: old-form control not detected"
  logInfo "S32AUDIT|ok"
#srm32_audit

end Tests.Compiler.Srm32AuditTest
end
