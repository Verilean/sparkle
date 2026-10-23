import Tests.Compiler.Srm26AuditExpected
import Tools.ShippingSrm26Order
-- BUILT (unit SRM26): dev runs a1-a2 (exit 1, audit-script errors), a3 (exit 0, S26AUDIT|ok); the final-SHA rebuild in REPORT-SRM26.md is the only final evidence.
-- Audit of the theorems of Tools/ShippingSrm26Order.lean (generic; NO topshare{M,Q} instance exists in this unit: K1 as an equation is neither exported nor proved).
-- (1) literal count guards and a binder table (index, binderInfo, name, isProp, type) for each theorem;
-- (2) BINDER-TABLE comparator against the expected statements generated from scripts/srm26/EXPECTED.txt (Srm26AuditExpected.lean): every row's binderInfo, name, isProp and (isDefEq) type, and the conclusion;
--     wrong-expected mutants rejected with the SPECIFIC row kind that differs (non-vacuous): ` ∧ True` on the Prop binder hK0 (type@9 only: index/name/binderInfo/isProp rows identical), an added data binder (name@4),
--     reordered binders (name@1), a wrong conclusion, and a K1 equation `regs = psN` added as a premise before hK0 (name@9);
-- (3) residual Props: no Prop binder restates the conclusion (control: wrapper detected); hK0 (K0N) is not defeq to the conclusion nor to any other binder; no binder is an equation on `List String`
--     (the K1 form; control: the K1 mutant's binder is detected);
-- (4) standard axioms; reachability of the composed reduction.
-- No instance theorem: one-witness check and forbidden-old-form closure audit are NOT APPLICABLE (nothing instantiates topshareM/Q).
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm26AuditTest
open Tests.Compiler.Srm26AuditExpected

theorem wrapper_mutation (p : Prop) (h : p) : p := h

def audited26 : List Name :=
  [``Tools.ShippingSrm26.nodup_getElem?_inj,
   ``Tools.ShippingSrm26.subset_of_length_le,
   ``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports,
   ``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired,
   ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired]

def pairs26 : List (Name × Name × Bool) :=
  [(``Tools.ShippingSrm26.nodup_getElem?_inj, ``Exp_nodup_getElem?_inj, false),
   (``Tools.ShippingSrm26.subset_of_length_le, ``Exp_subset_of_length_le, true),
   (``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports, ``Exp_sourceRegsAreSlots_regs_of_ports, true),
   (``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired, ``Exp_sourceRegsAreSlots_of_wired, true),
   (``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired, ``Exp_shippedRegsAreSlots_of_wired, true)]

/-- (mutant, expected row kind that must be the FIRST difference to the real statement) -/
def mutants26 : List (Name × String) :=
  [(``Exp_mut_withTrue, "type@9"), (``Exp_mut_addedBinder, "name@4"), (``Exp_mut_reordered, "name@1"),
   (``Exp_mut_wrongConclusion, "concl"), (``Exp_mut_k1Premise, "name@9")]

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Binder-table comparator: first difference between theorem type `t` and expected type `e`
(row index, then binderInfo, name (if `names`), isProp, type up to `isDefEq`; then the conclusion). -/
def tableCmp (t e : Expr) (names : Bool) : MetaM (Option String) :=
  forallTelescope t fun xs concl => do
    let mut e := e
    let mut i : Nat := 0
    for x in xs do
      match e with
      | .forallE n d b bi =>
        let dx ← x.fvarId!.getDecl
        if bi != dx.binderInfo then return some s!"info@{i}"
        if names && bi != .instImplicit && n != dx.userName then return some s!"name@{i}"
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

/-- does a Prop hypothesis of `thm` restate its conclusion (reducible `isDefEq`)? -/
def restatesConclusion (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← isProp d.type) then
        if (← withReducible (isDefEq d.type concl)) then return true
    return false

/-- is some binder an equation between lists of strings (the K1 form `regs = …`)? -/
def hasListStringEq (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.type.isAppOf ``Eq then
        let a := d.type.getAppArgs
        if a.size == 3 && (← isDefEq a[0]! (← mkAppM ``List #[mkConst ``String])) then return true
    return false

elab "#srm26_audit" : command => liftTermElabM do
  unless audited26.length == 5 && pairs26.length == 5 && mutants26.length == 5 do throwError "SRM26 AUDIT FAILED: literal count guard"
  -- (1) binder tables
  for t in audited26 do
    let ci ← getConstInfo t
    logInfo m!"S26THM|{t}"
    forallTelescope ci.type fun xs concl => do
      let mut i : Nat := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        logInfo m!"S26PREM|{t}|{i}|{repr d.binderInfo}|{d.userName}|{← isProp d.type}|{← ppExpr d.type}"
        i := i + 1
      logInfo m!"S26CONC|{t}|{← ppExpr concl}"
  -- (2) comparator
  for (t, e, nm) in pairs26 do
    let ci ← getConstInfo t
    match ← tableCmp ci.type (← expType e) nm with
    | none => logInfo m!"S26TABLEOK|{t}|{e}"
    | some r => throwError "SRM26 AUDIT FAILED: {t} differs from {e} at {r}"
  let real ← getConstInfo ``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports
  for (mname, want) in mutants26 do
    let mt ← expType mname
    unless (← isProp mt) do throwError "SRM26 AUDIT FAILED: mutant {mname} is not a Prop"
    match ← tableCmp real.type mt true with
    | none => throwError "SRM26 AUDIT FAILED: mutant {mname} ACCEPTED by the binder-table comparator"
    | some r =>
      unless r == want do throwError "SRM26 AUDIT FAILED: mutant {mname} rejected for {r}, expected {want}"
      logInfo m!"S26MUTREJECT|{mname}|{r}"
  -- (3) residual Props
  for t in audited26 do
    if (← restatesConclusion t) then throwError "SRM26 AUDIT FAILED: a hypothesis of {t} restates its conclusion"
    if (← hasListStringEq (← getConstInfo t).type) then throwError "SRM26 AUDIT FAILED: {t} has a List String equation binder (K1 form)"
  unless (← restatesConclusion ``Tests.Compiler.Srm26AuditTest.wrapper_mutation) do
    throwError "SRM26 AUDIT FAILED: control wrapper not detected"
  unless (← hasListStringEq (← expType ``Exp_mut_k1Premise)) do throwError "SRM26 AUDIT FAILED: K1-form control not detected"
  for t in [``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports, ``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired,
            ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired] do
    let ci ← getConstInfo t
    forallTelescope ci.type fun xs concl => do
      let hK0 := xs.back!
      let dK ← hK0.fvarId!.getDecl
      unless dK.userName == `hK0 do throwError "SRM26 AUDIT FAILED: last binder of {t} is not hK0"
      if (← isDefEq dK.type concl) then throwError "SRM26 AUDIT FAILED: hK0 of {t} defeq to its conclusion"
      for x in xs.pop do
        let d ← x.fvarId!.getDecl
        if (← isProp d.type) && (← isDefEq d.type dK.type) then throwError "SRM26 AUDIT FAILED: hK0 of {t} defeq to premise {d.userName}"
      logInfo m!"S26RESIDUAL|{t}|hK0 (K0N) distinct from conclusion and every other binder"
  -- (4) closures
  for t in audited26 do
    let ax ← Lean.collectAxioms t
    for a in ax do
      unless stdAx.contains a do throwError "SRM26 AUDIT FAILED: non-standard axiom {a} in {t}"
    logInfo m!"S26AXIOMS|{t}|{ax.toList}"
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
            if ((`Tools.ShippingSrm26).isPrefixOf d || (`Tools.ShippingSrm25Init).isPrefixOf d) && !seen.contains d then todo := d :: todo
    return seen
  let r := ← reach ``Tools.ShippingSrm26.shippedRegsAreSlots_of_wired
  for n in [``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired, ``Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports,
            ``Tools.ShippingSrm26.subset_of_length_le, ``Tools.ShippingSrm26.nodup_getElem?_inj,
            ``Tools.ShippingSrm25Init.shippedRegsAreSlots_of_source] do
    unless r.contains n do throwError "SRM26 AUDIT FAILED: {n} not reachable from shippedRegsAreSlots_of_wired"
  logInfo "S26INSTANCES|none (one-witness and forbidden-old-form closure audit not applicable)"
  logInfo "S26AUDIT|ok"
#srm26_audit

end Tests.Compiler.Srm26AuditTest
end
