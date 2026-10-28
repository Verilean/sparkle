import Tests.Compiler.Srm31AuditExpected
import Tests.Compiler.Srm9ComposedTest
import Tools.ShippingSlotRegsRun
-- BUILT (unit SRM31): dev runs a3, a4 (exit 0, S31AUDIT|ok); a1,a2 exit 1 (generated-file opens; script bug); dev runs are in REPORT-SRM31.md, the final-SHA rebuild there is the only final evidence.
-- Audit of Tools/ShippingSrm31Core.lean and Tests/Compiler/Srm31EndpointTest.lean (4 theorems):
-- (1) literal count guards; full binder tuples printed per theorem (S31PREM) and a marker per theorem (S31THM);
-- (2) STRUCTURAL comparator `walk` (forall rows: binderInfo, name when not hygienic, isProp, isDefEq type; Exists / And descended; leaf isDefEq) of each theorem against the generated Exp_* statement
--     (scripts/srm31/gen_audit_expected.py, text of the ORIGINAL theorems + EXPECTED.txt);
-- (3) the new endpoints differ from the ORIGINAL `Srm9ComposedTest.topshare{M,Q}_hierC_at_free` in EXACTLY ONE row (the former hstR), everything else (all other binders, the conclusion) is defeq;
-- (4) wrong-expected mutants rejected with the specific kind: hstR kept; hinit dropped; conclusion weakened; ` ∧ True` on a Prop binder (row invariants: still a Prop, same binderInfo); an added data binder; reordered binders;
--     each mutant is non-vacuous (a Prop, accepted when compared with itself);
-- (5) no relabel: no binder of a new theorem mentions seqRegs (= is hstR or its restatement), no Prop binder restates the conclusion; controls detect both on the original / a wrapper;
-- (6) one witness: `topshare{M,Q}_composedNW` occurs exactly once in each instance proof; closure: standard axioms, forbidden old-form roots absent, with positive controls.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm31AuditTest
open Tests.Compiler.Srm31AuditExpected

theorem wrapper_mutation (p : Prop) (h : p) : p := h

def audited31 : List Name :=
  [``Tools.ShippingSrm31.hstR_of_wired_slots, ``Tools.ShippingSrm31.machine_ships_hierC_at_nw,
   ``Tests.Compiler.Srm31EndpointTest.topshareM_hierC_at_nw, ``Tests.Compiler.Srm31EndpointTest.topshareQ_hierC_at_nw]

def pairs31 : List (Name × Name) :=
  [(audited31[0]!, ``Exp_aux), (audited31[1]!, ``Exp_generic), (audited31[2]!, ``Exp_M), (audited31[3]!, ``Exp_Q)]

/-- (real theorem, mutant, expected first-difference kind) -/
def mutants31 : List (Name × Name × String) :=
  [(audited31[1]!, ``Exp_generic_mut_hstrKept, "type"),
   (audited31[2]!, ``Exp_M_mut_hstrKept, "type"), (audited31[2]!, ``Exp_M_mut_noHinit, "type"), (audited31[2]!, ``Exp_M_mut_weak, "leaf"),
   (audited31[2]!, ``Exp_M_mut_withTrue, "type"), (audited31[2]!, ``Exp_M_mut_addedBinder, "info"), (audited31[2]!, ``Exp_M_mut_reordered, "type"),
   (audited31[3]!, ``Exp_Q_mut_hstrKept, "type"), (audited31[3]!, ``Exp_Q_mut_noHinit, "type"), (audited31[3]!, ``Exp_Q_mut_weak, "leaf"),
   (audited31[3]!, ``Exp_Q_mut_withTrue, "type"), (audited31[3]!, ``Exp_Q_mut_addedBinder, "info"), (audited31[3]!, ``Exp_Q_mut_reordered, "type")]

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Structural comparator: the list of differences (kind@path), empty iff the statements agree row by row. -/
partial def walk (path : String) (a e : Expr) : MetaM (List String) := do
  match a, e with
  | .forallE n1 d1 b1 bi1, .forallE n2 d2 _ bi2 =>
    let mut diffs : List String := []
    if bi1 != bi2 then diffs := diffs ++ [s!"info@{path}/{n1}"]
    if bi1 != .instImplicit && !n1.hasMacroScopes && !n2.hasMacroScopes && n1 != n2 then diffs := diffs ++ [s!"name@{path}/{n1}"]
    if (← isProp d1) != (← isProp d2) then diffs := diffs ++ [s!"isProp@{path}/{n1}"]
    unless (← isDefEq d1 d2) do diffs := diffs ++ [s!"type@{path}/{n1}"]
    let rest ← withLocalDecl n1 bi1 d1 fun x => do
      let .forallE _ _ b2 _ := e | return ["leaf@impossible"]
      walk (path ++ "/" ++ toString n1) (b1.instantiate1 x) (b2.instantiate1 x)
    return diffs ++ rest
  | _, _ =>
    if a.isAppOfArity ``Exists 2 && e.isAppOfArity ``Exists 2 then
      let ty1 := a.getArg! 0
      let ty2 := e.getArg! 0
      let mut diffs : List String := []
      unless (← isDefEq ty1 ty2) do diffs := diffs ++ [s!"type@{path}/∃"]
      match a.getArg! 1, e.getArg! 1 with
      | .lam n1 t1 b1 bi1, .lam n2 _ b2 _ =>
        if !n1.hasMacroScopes && !n2.hasMacroScopes && n1 != n2 then diffs := diffs ++ [s!"name@{path}/∃{n1}"]
        let rest ← withLocalDecl n1 bi1 t1 fun x => walk (path ++ "/∃" ++ toString n1) (b1.instantiate1 x) (b2.instantiate1 x)
        return diffs ++ rest
      | _, _ => return diffs ++ [s!"leaf@{path}/∃body"]
    else if a.isAppOfArity ``And 2 && e.isAppOfArity ``And 2 then
      let l ← walk (path ++ "/∧L") (a.getArg! 0) (e.getArg! 0)
      let r ← walk (path ++ "/∧R") (a.getArg! 1) (e.getArg! 1)
      return l ++ r
    else if (← isDefEq a e) then return [] else return [s!"leaf@{path}"]

def kindOf (s : String) : String := (s.splitOn "@").head!

def expType (n : Name) : MetaM Expr := do
  let ei ← getConstInfo n
  return ei.value?.getD (mkConst n)

def thmType (n : Name) : MetaM Expr := return (← getConstInfo n).type

/-- all binder types of a statement, descended through ∀ / ∃ / ∧ -/
partial def binderTypes (e : Expr) : MetaM (Array Expr) := do
  match e with
  | .forallE n d b bi =>
    let rest ← withLocalDecl n bi d fun x => binderTypes (b.instantiate1 x)
    return #[d] ++ rest
  | _ =>
    if e.isAppOfArity ``Exists 2 then
      match e.getArg! 1 with
      | .lam n t b bi => withLocalDecl n bi t fun x => binderTypes (b.instantiate1 x)
      | _ => return #[]
    else if e.isAppOfArity ``And 2 then
      return (← binderTypes (e.getArg! 0)) ++ (← binderTypes (e.getArg! 1))
    else return #[]

def mentionsSeqRegs (e : Expr) : Bool := e.getUsedConstants.contains ``Sparkle.IR.OptCheck.seqRegs

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
  let mut fuel := 600000
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

elab "#srm31_audit" : command => liftTermElabM do
  unless audited31.length == 4 && pairs31.length == 4 && mutants31.length == 13 do throwError "SRM31 AUDIT FAILED: literal count guard"
  -- (1) binder tables + markers
  for t in audited31 do
    let ci ← getConstInfo t
    logInfo m!"S31THM|{t}"
    forallTelescope ci.type fun xs concl => do
      let mut i : Nat := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        logInfo m!"S31PREM|{t}|{i}|{repr d.binderInfo}|{d.userName}|{← isProp d.type}"
        i := i + 1
      logInfo m!"S31CONC|{t}|{concl.getAppFn.constName?}"
  -- (2) comparator against the generated expected statements
  for (t, e) in pairs31 do
    match ← walk "" (← thmType t) (← expType e) with
    | [] => logInfo m!"S31TABLEOK|{t}|{e}"
    | d :: _ => throwError "SRM31 AUDIT FAILED: {t} differs from {e}: {d}"
  -- (3) the endpoints = the ORIGINAL endpoints minus exactly one row
  for (t, o, eo) in [(audited31[2]!, ``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free, ``Exp_M_orig),
                     (audited31[3]!, ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free, ``Exp_Q_orig)] do
    -- Exp_*_orig is a def: compare its body
    match ← walk "" (← expType eo) (← thmType o) with
    | [] => pure ()
    | d :: _ => throwError "SRM31 AUDIT FAILED: generated {eo} differs from the actual original {o}: {d}"
    let ds ← walk "" (← thmType t) (← thmType o)
    unless ds.length == 1 && kindOf ds.head! == "type" do
      throwError "SRM31 AUDIT FAILED: {t} vs {o}: expected exactly one differing row, got {ds}"
    logInfo m!"S31ONEROW|{t}|{o}|{ds}"
    -- REPLACEMENT row (REVIEW S1/S4): one Prop binder replaced; hinitW is NOT a binder of the instance
    forallTelescope (← thmType t) fun xs _ => do
      for x in xs do
        if (← x.fvarId!.getDecl).userName == `hinitW then throwError "SRM31 AUDIT FAILED: hinitW is a binder of {t}"
    logInfo m!"S31REPLACEMENT|{t}|row hstR -> hWd (width link, PREMISE); hinitW not a binder; hstR NOT discharged"
  -- (4) mutants
  for (t, mname, want) in mutants31 do
    let mt ← expType mname
    unless (← isProp mt) do throwError "SRM31 AUDIT FAILED: mutant {mname} is not a Prop"
    unless (← walk "" mt mt).isEmpty do throwError "SRM31 AUDIT FAILED: mutant {mname} not self-equal (vacuous)"
    match ← walk "" (← thmType t) mt with
    | [] => throwError "SRM31 AUDIT FAILED: mutant {mname} ACCEPTED"
    | d :: _ =>
      unless kindOf d == want do throwError "SRM31 AUDIT FAILED: mutant {mname} rejected for {d}, expected kind {want}"
      logInfo m!"S31MUTREJECT|{mname}|{d}"
  -- (5) no relabel
  for t in audited31 do
    if (← restatesConclusion t) then throwError "SRM31 AUDIT FAILED: a hypothesis of {t} restates its conclusion"
    if t != audited31[0]! then
      for bt in ← binderTypes (← thmType t) do
        if mentionsSeqRegs bt then throwError "SRM31 AUDIT FAILED: a binder of {t} mentions seqRegs (hstR or a restatement)"
  unless (← restatesConclusion ``Tests.Compiler.Srm31AuditTest.wrapper_mutation) do
    throwError "SRM31 AUDIT FAILED: control wrapper not detected"
  for o in [``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free, ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free] do
    let bs ← binderTypes (← thmType o)
    unless bs.any mentionsSeqRegs do throwError "SRM31 AUDIT FAILED: no-relabel control: hstR not detected in {o}"
  logInfo "S31NORELABEL|no binder of a new theorem mentions seqRegs; the original endpoints' hstR binder is detected by the same predicate (control)"
  -- (6) one witness and closure
  let forbidden : List Name := [``Tools.ShippingMachineShipsDepth.composedG_of_NW, ``Tools.ShippingSlotRegsRun.slotRegs_runMT,
    ``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired]
  for (inst, comp) in [(audited31[2]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_composedNW),
                       (audited31[3]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_composedNW)] do
    let ci ← getConstInfo inst
    let cnt := countConst comp (valueOf ci)
    unless cnt == 1 do throwError "SRM31 AUDIT FAILED: {comp} occurs {cnt} times in {inst}, expected 1 (one witness)"
    let cg := countConst ``Tools.ShippingSrm31.machine_ships_hierC_at_nw (valueOf ci)
    unless cg == 1 do throwError "SRM31 AUDIT FAILED: the generic theorem occurs {cg} times in {inst}"
    let r ← reachAll inst
    for f in forbidden do
      if r.contains f then throwError "SRM31 AUDIT FAILED: forbidden root {f} in the closure of {inst}"
    for must in [``Tools.ShippingSrm31.hstR_of_wired_slots, ``Tools.ShippingSrm28.sourceRegsAreSlots_of_wired_all, comp] do
      unless r.contains must do throwError "SRM31 AUDIT FAILED: {must} missing from the closure of {inst}"
    logInfo m!"S31ONEWITNESS|{inst}|{comp} once; forbidden roots absent"
  for t in audited31 do
    let ax ← Lean.collectAxioms t
    for a in ax do
      unless stdAx.contains a do throwError "SRM31 AUDIT FAILED: non-standard axiom {a} in {t}"
    logInfo m!"S31AXIOMS|{t}|{ax.toList}"
  -- positive controls for the forbidden roots
  unless (← reachAll ``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free).contains ``Tools.ShippingMachineShipsDepth.composedG_of_NW do
    throwError "SRM31 AUDIT FAILED: forbidden-root control (composedG_of_NW) not detected"
  unless (← reachAll ``Tools.ShippingSlotRegsRun.slotRegs_runMT).contains ``Tools.ShippingChildInv.MachineClosesAt do
    throwError "SRM31 AUDIT FAILED: forbidden-root control (MachineClosesAt) not detected"
  logInfo "S31AUDIT|ok"
#srm31_audit

end Tests.Compiler.Srm31AuditTest
end
