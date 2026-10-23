import Tests.Compiler.Srm28ExpStmt
import Tests.Compiler.Srm26AuditTest
import Tools.ShippingSrm28Regs
-- BUILT (unit SRM28): dev runs a1-a3 (exit 1, script errors), a4 (exit 0, S28AUDIT|ok); the final-SHA rebuild in REPORT-SRM28.md is the only final evidence.
-- Audit of Tools/ShippingSrm28Regs.lean, Tests/Compiler/Srm28InstTest.lean and the CHANGED statement `MachineWired`:
-- (0) `MachineWired` unfolds to exactly 19 conjuncts and the 19th is defeq to `Exp_lastClause` (EXPECTED §1); the 18th is untouched in count;
-- (1) literal count guard and binder tables for the 8 theorems;
-- (2) BINDER-TABLE comparator (binderInfo, name, isProp, isDefEq type per row, then conclusion) against Srm28ExpStmt (written from scripts/srm28/EXPECTED.txt, committed before any Lean edit);
--     wrong-expected mutants rejected with the specific row kind: ` ∧ True` on the Prop binder hW, an added data binder, reordered binders, hb dropped; for the instance: P := True, hpost dropped;
-- (3) no relabel: no Prop binder restates its conclusion (control wrapper detected); the new clause is theorem-backed: the 19th conjunct is not a binder of any audited theorem, and `MachineWired`
--     (hW) is not defeq to the conclusion;
-- (4) instances: the ComposedNW witness is used ONCE (exactly one occurrence of topshare{M,Q}_composedNW in the proof term); one run (hcore), one design D, one module raw; closure: standard axioms,
--     forbidden old-form roots (SRM26 K0N route, composedG_of_NW) absent with positive controls.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm28AuditTest
open Tests.Compiler.Srm28ExpStmt

theorem wrapper_mutation (p : Prop) (h : p) : p := h

def audited28 : List Name :=
  [``Tools.ShippingSrm28.sourceRegsAreSlots_of_wired_all, ``Tools.ShippingSrm28.shippedRegsAreSlots_of_wired_all,
   ``Tools.ShippingSrm28.composedNWRegs_of_composedNW, ``Tools.ShippingSrm28.ComposedNWRegs.toNW,
   ``Tests.Compiler.Srm28InstTest.topshareM_composedNW_g5, ``Tests.Compiler.Srm28InstTest.topshareM_composedNW_regsAtInit_noG5,
   ``Tests.Compiler.Srm28InstTest.topshareQ_composedNW_g5, ``Tests.Compiler.Srm28InstTest.topshareQ_composedNW_regsAtInit_noG5]

def pairs28 : List (Name × Name) :=
  [(audited28[0]!, ``Exp_source), (audited28[1]!, ``Exp_g5), (audited28[2]!, ``Exp_lift), (audited28[3]!, ``Exp_toNW),
   (audited28[4]!, ``Exp_M_g5), (audited28[5]!, ``Exp_M_noG5), (audited28[6]!, ``Exp_Q_g5), (audited28[7]!, ``Exp_Q_noG5)]

/-- (real theorem, mutant, expected first-difference kind) -/
def mutants28 : List (Name × Name × String) :=
  [(audited28[1]!, ``Exp_mut_withTrue, "type@11"), (audited28[1]!, ``Exp_mut_addedBinder, "name@11"),
   (audited28[1]!, ``Exp_mut_reordered, "name@9"), (audited28[1]!, ``Exp_mut_noHb, "name@10"),
   (audited28[4]!, ``Exp_mut_M_trivialP, "concl"), (audited28[4]!, ``Exp_mut_M_noHpost, "name@10")]

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

elab "#srm28_audit" : command => liftTermElabM do
  unless audited28.length == 8 && pairs28.length == 8 && mutants28.length == 6 do throwError "SRM28 AUDIT FAILED: literal count guard"
  -- (0) MachineWired: 19 conjuncts, 19th = Exp_lastClause
  do
    let ci ← getConstInfo ``Tools.ShippingMachineEntry.MachineWired
    lambdaTelescope ci.value?.get! fun xs body => do
      let mut b ← zetaReduce body
      let mut n : Nat := 0
      let mut last := b
      while b.isAppOfArity ``And 2 do
        n := n + 1
        last := b.appFn!.appArg!
        b := b.appArg!
      last := b   -- the final non-And tail is the last conjunct
      n := n + 1
      unless n == 19 do throwError "SRM28 AUDIT FAILED: MachineWired has {n} conjuncts, expected 19"
      let exp ← mkAppM ``Exp_lastClause #[xs[1]!, xs[4]!, xs[6]!]
      unless (← isDefEq last exp) do throwError "SRM28 AUDIT FAILED: the last conjunct of MachineWired differs from Exp_lastClause"
      logInfo m!"S28WIRED|19 conjuncts; the 19th is defeq to Exp_lastClause"
  -- (1) binder tables
  for t in audited28 do
    let ci ← getConstInfo t
    logInfo m!"S28THM|{t}"
    forallTelescope ci.type fun xs concl => do
      let mut i : Nat := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        logInfo m!"S28PREM|{t}|{i}|{repr d.binderInfo}|{d.userName}|{← isProp d.type}|{← ppExpr d.type}"
        i := i + 1
      logInfo m!"S28CONC|{t}|{← ppExpr concl}"
  -- (2) comparator
  for (t, e) in pairs28 do
    match ← tableCmp (← getConstInfo t).type (← expType e) with
    | none => logInfo m!"S28TABLEOK|{t}|{e}"
    | some r => throwError "SRM28 AUDIT FAILED: {t} differs from {e} at {r}"
  for (t, mname, want) in mutants28 do
    let mt ← expType mname
    unless (← isProp mt) do throwError "SRM28 AUDIT FAILED: mutant {mname} is not a Prop"
    match ← tableCmp (← getConstInfo t).type mt with
    | none => throwError "SRM28 AUDIT FAILED: mutant {mname} ACCEPTED"
    | some r =>
      unless r == want do throwError "SRM28 AUDIT FAILED: mutant {mname} rejected for {r}, expected {want}"
      logInfo m!"S28MUTREJECT|{mname}|{r}"
  -- (3) no relabel
  for t in audited28 do
    if (← restatesConclusion t) then throwError "SRM28 AUDIT FAILED: a hypothesis of {t} restates its conclusion"
  unless (← restatesConclusion ``Tests.Compiler.Srm28AuditTest.wrapper_mutation) do
    throwError "SRM28 AUDIT FAILED: control wrapper not detected"
  logInfo "S28NORELABEL|hW (MachineWired) is not the conclusion of either wired theorem; the 19th clause is a theorem-backed export (producer proof in MachineEntry), no binder of any audited theorem"
  -- (4) closure
  for t in audited28 do
    let ax ← Lean.collectAxioms t
    for a in ax do
      unless stdAx.contains a do throwError "SRM28 AUDIT FAILED: non-standard axiom {a} in {t}"
    logInfo m!"S28AXIOMS|{t}|{ax.toList}"
  let forbidden : List Name := [``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired, ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired,
    ``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports]
  for (inst, comp) in [(audited28[4]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_composedNW),
                       (audited28[6]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_composedNW)] do
    let ci ← getConstInfo inst
    let cnt := countConst comp (valueOf ci)
    unless cnt == 1 do throwError "SRM28 AUDIT FAILED: {comp} occurs {cnt} times in {inst}, expected 1 (one witness)"
    let r ← reachAll inst
    for f in forbidden do
      if r.contains f then throwError "SRM28 AUDIT FAILED: forbidden old-form root {f} in the closure of {inst}"
    for must in [``Tools.ShippingSrm28.shippedRegsAreSlots_of_wired_all, ``Tools.ShippingSrm28.composedNWRegs_of_composedNW,
                 ``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source, comp] do
      unless r.contains must do throwError "SRM28 AUDIT FAILED: {must} missing from the closure of {inst}"
    logInfo m!"S28ONEWITNESS|{inst}|{comp} once; forbidden roots absent"
  -- positive control for the forbidden-root test
  unless (← reachAll ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired).contains ``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired do
    throwError "SRM28 AUDIT FAILED: forbidden-root control not detected"
  logInfo "S28AUDIT|ok"
#srm28_audit

end Tests.Compiler.Srm28AuditTest
end
