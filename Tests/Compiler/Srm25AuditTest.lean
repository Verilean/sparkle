import Tests.Compiler.Srm25ExpStmt
import Tools.ShippingSrm25Init
-- BUILT (unit SRM25): dev runs i1-i5 (exit 1, audit-script errors), i6 (exit 0); audit of the 3 theorems of Tools/ShippingSrm25Init.lean (generic; there are NO topshare instances/corollaries in this unit: G5 for the ComposedG witness regs is OPEN).
-- (1) literal count guard (3) and binder table printed (index, binderInfo, name, isProp, type) for each theorem;
-- (2) `isDefEq` of each theorem's type against the expected statement written from scripts/srm25/EXPECTED.txt; three mutated expected forms (reset value dropped, hierGate dropped, ` ∧ True` on the source premise) are REJECTED, each non-vacuous;
-- (3) no relabelling: the source premise type `SourceRegsAreSlots b regs slots` is NOT defeq to G5 (control: a `p → p` wrapper IS detected by the same test);
--     the reduction theorem's premise binder `hS` is a Prop not defeq to its conclusion;
-- (4) closure: standard axioms only for all three; the reduction proof term uses `refineCheck_regInit` and `shippedRegInit_of_hierGate`.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm25AuditTest

theorem wrapper_mutation (p : Prop) (h : p) : p := h

def audited25 : List Name :=
  [``Tools.ShippingSrm25Init.refineCheck_regInit,
   ``Tools.ShippingSrm25Init.shippedRegInit_of_hierGate,
   ``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source]

def pairs25 : List (Name × Name) :=
  [(``Tools.ShippingSrm25Init.refineCheck_regInit, ``Tests.Compiler.Srm25ExpStmt.Exp_regInit),
   (``Tools.ShippingSrm25Init.shippedRegInit_of_hierGate, ``Tests.Compiler.Srm25ExpStmt.Exp_shippedInit),
   (``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source, ``Tests.Compiler.Srm25ExpStmt.Exp_reduction)]

def mutPairs25 : List (Name × Name) :=
  [(``Tools.ShippingSrm25Init.shippedRegInit_of_hierGate, ``Tests.Compiler.Srm25ExpStmt.Exp_mut_initDropped),
   (``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source, ``Tests.Compiler.Srm25ExpStmt.Exp_mut_noGate),
   (``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source, ``Tests.Compiler.Srm25ExpStmt.Exp_mut_withTrue),
   (``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source, ``Tests.Compiler.Srm25ExpStmt.Exp_mut_addedBinder),
   (``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source, ``Tests.Compiler.Srm25ExpStmt.Exp_mut_reordered)]

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- does a hypothesis of `thm` restate its conclusion (reducible `isDefEq`)? -/
def restatesConclusion (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← isProp d.type) then
        if (← withReducible (isDefEq d.type concl)) then return true
    return false

elab "#srm25_audit" : command => liftTermElabM do
  unless audited25.length == 3 do throwError "SRM25 AUDIT FAILED: literal count guard"
  -- (1) binder tables
  for t in audited25 do
    let ci ← getConstInfo t
    logInfo m!"S25THM|{t}"
    forallTelescope ci.type fun xs concl => do
      let mut i : Nat := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        logInfo m!"S25PREM|{t}|{i}|{repr d.binderInfo}|{d.userName}|{← isProp d.type}|{← ppExpr d.type}"
        i := i + 1
      logInfo m!"S25CONC|{t}|{← ppExpr concl}"
  -- (2) expected statements
  for (t, e) in pairs25 do
    let ci ← getConstInfo t
    let ei ← getConstInfo e
    unless (← isDefEq ci.type (ei.value?.getD (mkConst e))) do
      throwError "SRM25 AUDIT FAILED: the statement of {t} is not defeq to its expected form {e}"
    logInfo m!"S25EXPDEFEQ|{t}|{e}|isDefEq"
  for (t, e) in mutPairs25 do
    let ci ← getConstInfo t
    let ei ← getConstInfo e
    -- non-vacuity: the mutated statement is a well-typed Prop
    unless (← isProp (ei.value?.getD (mkConst e))) do throwError "SRM25 AUDIT FAILED: mutation {e} is not a Prop"
    if (← isDefEq ci.type (ei.value?.getD (mkConst e))) then
      throwError "SRM25 AUDIT FAILED: the mutated expected statement {e} was ACCEPTED for {t}"
    logInfo m!"S25MUTREJECT|{t}|{e}"
  -- (3) no relabelling, with control
  for t in audited25 do
    if (← restatesConclusion t) then throwError "SRM25 AUDIT FAILED: a hypothesis of {t} restates its conclusion"
  unless (← restatesConclusion ``Tests.Compiler.Srm25AuditTest.wrapper_mutation) do
    throwError "SRM25 AUDIT FAILED: control wrapper not detected"
  -- G5 vs source premise: distinct Props at a generic instance
  do
    let ci ← getConstInfo ``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source
    forallTelescope ci.type fun xs concl => do
      let hS := xs.back!
      let dS ← hS.fvarId!.getDecl
      if (← isDefEq dS.type concl) then throwError "SRM25 AUDIT FAILED: premise hS is defeq to G5"
      logInfo m!"S25NORELABEL|hS vs G5|distinct"
  -- (4) closures
  for t in audited25 do
    let ax ← Lean.collectAxioms t
    for a in ax do
      unless stdAx.contains a do throwError "SRM25 AUDIT FAILED: non-standard axiom {a} in {t}"
    logInfo m!"S25AXIOMS|{t}|{ax.toList}"
  -- constants of the SRM25 namespace reachable from `n` (auxiliary matchers/proofs included)
  let reach (n : Name) : MetaM (Std.HashSet Name) := do
    let mut seen : Std.HashSet Name := {}
    let mut todo : List Name := [n]
    let mut fuel := 2000
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
            if (`Tools.ShippingSrm25Init).isPrefixOf d && !seen.contains d then todo := d :: todo
    return seen
  unless (← reach ``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source).contains ``Tools.ShippingSrm25Init.shippedRegInit_of_hierGate do
    throwError "SRM25 AUDIT FAILED: shippedRegInit_of_hierGate not reachable from the reduction"
  unless (← reach ``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source).contains ``Tools.ShippingSrm25Init.refineCheck_regInit do
    throwError "SRM25 AUDIT FAILED: refineCheck_regInit not reachable from the reduction"
  logInfo "S25AUDIT|ok"
#srm25_audit

end Tests.Compiler.Srm25AuditTest
end
