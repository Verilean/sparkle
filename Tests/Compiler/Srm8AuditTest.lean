import Tools.ShippingKidsChildIfaceM
import Tests.Compiler.Srm8ChainTest
import Tests.Compiler.ParentHoutTyHTest
import Tests.Compiler.Srm4ParentTest
import Tests.Compiler.Srm4ParentQTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm8AuditExpected
import Tools.ShippingOneOutHead
import Tools.ShippingSrm8Bridge
-- UNBUILT (unit SRM8): see STATUS-SRM8.md for run names; the final-SHA rebuild is in REPORT-SRM8.md.
-- SCOPE (SRM8, chain audit).  (1) PREMISE TABLE: for each audited theorem (the memory-free endpoints, the consumers of `designCheck`, the SRM4/SRM5 memory-bearing supplies, the new bridge endpoint) every binder
-- `(index, binderInfo, name, isProp, type)` is printed as `S8PREM`/`S8DATA` and the WHOLE table must EQUAL the committed `Tests/Compiler/Srm8AuditExpected.lean` and `scripts/srm8/PREMISES.txt` (exact), with a literal count guard
-- and three NEGATIVE fixtures (changed Prop binder type, added data binder, reordered binders).  REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm8AuditTest > LOG 2>&1; python3 scripts/srm8/gen_audit.py LOG`.
-- (2) SUPPLY MAP: `scripts/srm8/SUPPLY.txt` classifies EVERY Prop binder (hypotheses and conclusion antecedents) of `design_at_free_h` and of `machine_ships_hierC_at_free` as PROVED-GENERIC / PROVED-INSTANCE / PREMISE / MISSING with the
-- supplying theorem(s) and owning unit; this test fails if a Prop binder has no row, a row has no binder, a status is invalid, or a cited theorem does not exist (a classification, not a proof of the cited statements beyond their existence
-- and standard axioms).  `scripts/srm8/gen_table.py` renders the table `scripts/srm8/SUPPLY_TABLE.md` from the printed rows plus SUPPLY.txt.
-- (3) CLOSURE: standard axioms for every audited theorem; the new `design_at_free_h` does NOT have `design_sv_runN` / `svBounds_of_checks` / `design_sv_all` in its closure (control: `design_at_free` does), and has no old-form boundary.
-- NOT guaranteed: that `HeightBridge` is true or provable (it is a PREMISE); that hypotheses are satisfiable beyond the instances; type strings are `ppExpr` renderings.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm8AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited8 theorems -/
def audited8 : List Name :=
  [``Tools.ShippingOneOutHead.machine_design_svH_free, ``Tools.ShippingShipsFree.machine_ships_hierC_at_free,
   ``Tools.ShippingShipsFree.design_at_free, ``Tools.ShippingSrm8Bridge.design_at_free_h,
   ``Tests.Compiler.ParentHoutTyTest.parent_noShips_noBdA_dcH,
   ``Tools.ShippingDesignSV.design_sv_runN, ``Tools.ShippingDesignSVBounds.svBounds_of_checks, ``Tools.ShippingDesignSVBack.design_sv_all,
   ``Tools.ShippingSrm5Height.hcheck_eq_designCheck,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_runFacts, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_outsCheck,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_kidsMasked, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designCheck_of_kidsPass,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_soundLA, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_traceXA,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_heightPass,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_runFacts, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_outsCheck,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_kidsMasked, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designCheck_of_kidsPass,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_soundLA, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_traceXA,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_heightPass]

/-- the theorems whose Prop binders are classified in `scripts/srm8/SUPPLY.txt` -/
def supplied : List Name := [``Tools.ShippingSrm8Bridge.design_at_free_h, ``Tools.ShippingShipsFree.machine_ships_hierC_at_free]

abbrev Row := Nat × String × String × Bool × String

/-- normalised binder name -/
def normName (n : String) : String := if (n.splitOn "_hyg").length > 1 then "_anon" else n

/-- rows `(index, binderInfo, name, isProp, type)` of the binders of a theorem's type -/
def premiseRows (thm : Name) : MetaM (List Row) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut rows : List Row := []
    let mut i := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let isP ← Meta.isProp d.type
      let bi := match d.binderInfo with
        | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst" | .default => "explicit"
      rows := rows ++ [(i, bi, normName d.userName.toString, isP, ((← ppExpr d.type).pretty 100000).replace "\n" " ")]
      i := i + 1
    return rows

/-- the text line of a row (the format of `scripts/srm8/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S8{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

/-- EXACT comparison of two whole tables: `none` iff equal, else the first difference -/
def tableDiff (a e : List (Name × List Row)) : Option String := Id.run do
  if a.length != e.length then return some s!"{a.length} theorems vs {e.length} expected"
  for ((n, rs), (n', rs')) in a.zip e do
    if n != n' then return some s!"theorem {n} vs expected {n'}"
    if rs.length != rs'.length then return some s!"{n}: {rs.length} binders vs {rs'.length} expected"
    for (r, r') in rs.zip rs' do
      if r != r' then return some s!"{n}: binder {r.1} differs: {rowLine n r} vs expected {rowLine n r'}"
  return none

/-- mutation 1: change the type of the first Prop binder (same name) -/
def mutType (t : List (Name × List Row)) : List (Name × List Row) :=
  match t.findIdx? (fun (_, rs) => rs.any (·.2.2.2.1)) with
  | none => t
  | some k => t.mapIdx fun j (n, rs) =>
    if j == k then
      let idx := (rs.findIdx? (·.2.2.2.1)).getD 0
      (n, rs.mapIdx fun i r => if i == idx then (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2 ++ " ") else r)
    else (n, rs)

/-- mutation 2: add a data binder to the first theorem -/
def mutAdd (t : List (Name × List Row)) : List (Name × List Row) :=
  t.mapIdx fun j (n, rs) => if j == 0 then (n, rs ++ [(rs.length, "implicit", "extraBinder", false, "Nat")]) else (n, rs)

/-- mutation 3: swap the first two binders of the first theorem that has two -/
def mutSwap (t : List (Name × List Row)) : List (Name × List Row) :=
  match t.findIdx? (fun (_, rs) => rs.length ≥ 2) with
  | none => t
  | some k => t.mapIdx fun j (n, rs) =>
    if j == k then (match rs with | r0 :: r1 :: rest => (n, r1 :: r0 :: rest) | _ => (n, rs)) else (n, rs)

/-- does a hypothesis of `thm` restate its conclusion (reducible `isDefEq`)? -/
def restatesConclusion (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← Meta.isProp d.type) then
        if (← withReducible (isDefEq d.type concl)) then return true
    return false



end Tests.Compiler.Srm8AuditTest

open Tests.Compiler.Srm8AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  unless (← restatesConclusion ``Tests.Compiler.Srm8AuditTest.wrapper_mutation) do throwError "SRM8 AUDIT FAILED: the wrapper control was not caught"
  unless audited8.length == 25 do throwError "SRM8 AUDIT FAILED: audited8 has {audited8.length} theorems, expected exactly 25"
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited8 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S8THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S8THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    -- the bridge's own endpoint has a hypothesis that is its conclusion? no.  (the memory-free endpoints are checked as well)
    if (← restatesConclusion thm) then throwError "SRM8 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  unless Tests.Compiler.Srm8AuditExpected.expectedRows.length == 25 do throwError "SRM8 AUDIT FAILED: the expected table has {Tests.Compiler.Srm8AuditExpected.expectedRows.length} entries, expected exactly 25"
  match tableDiff actual Tests.Compiler.Srm8AuditExpected.expectedRows with
  | some msg => throwError "SRM8 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm8AuditExpected.lean: {msg}"
  | none => pure ()
  let txt ← IO.FS.readFile "scripts/srm8/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM8 AUDIT FAILED: scripts/srm8/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM8 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm8AuditExpected.expectedRows with
    | none => throwError "SRM8 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S8FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S8TABLE|{audited8.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm8/PREMISES.txt"
  -- (2) SUPPLY MAP
  let sup ← IO.FS.readFile "scripts/srm8/SUPPLY.txt"
  let supRows := (sup.splitOn "\n").filter (fun l => l != "" && !l.startsWith "#") |>.map (·.splitOn "|")
  let validStatus := ["PROVED-GENERIC", "PROVED-INSTANCE", "PREMISE", "MISSING"]
  for r in supRows do
    unless r.length == 6 do throwError "SRM8 AUDIT FAILED: SUPPLY.txt row {r} does not have 6 fields (thm|binder|status|suppliers|owner|note)"
    unless validStatus.contains r[2]! do throwError "SRM8 AUDIT FAILED: SUPPLY.txt row {r}: invalid status"
    for s in (r[3]!.splitOn ",").filter (· != "-") do
      unless (← getEnv).contains s.toName do throwError "SRM8 AUDIT FAILED: SUPPLY.txt cites {s}, which does not exist"
      stdAxioms s.toName
  let mut covered := 0
  for thm in supplied do
    let rows ← premiseRows thm
    let pr := rows.filter (·.2.2.2.1)
    for p in pr do
      let key := if p.2.2.1 == "_anon" then s!"anon:{p.1}" else p.2.2.1
      let m := supRows.filter fun r => r[0]! == thm.toString && r[1]! == key
      unless m.length == 1 do throwError "SRM8 AUDIT FAILED: Prop binder {key} of {thm} has {m.length} SUPPLY.txt rows (expected exactly 1)"
      covered := covered + 1
      logInfo m!"S8SUPPLY|{thm}|{key}|{m[0]![2]!}|{m[0]![3]!}|{m[0]![4]!}|{p.2.2.2.2}"
  unless covered == supRows.length do throwError "SRM8 AUDIT FAILED: SUPPLY.txt has {supRows.length} rows but {covered} Prop binders are covered (a row names no binder)"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingKidFacts.KidFacts]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM8 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM8 AUDIT FAILED: control walk found no old-form constant"
  let consumers : List Name := [``Tools.ShippingDesignSV.design_sv_runN, ``Tools.ShippingDesignSVBounds.svBounds_of_checks, ``Tools.ShippingDesignSVBack.design_sv_all]
  let clOld ← depClosure ``Tools.ShippingShipsFree.design_at_free
  for u in consumers do
    unless clOld.contains u do throwError "SRM8 AUDIT FAILED: control: design_at_free does not use {u}"
  let clNew ← depClosure ``Tools.ShippingSrm8Bridge.design_at_free_h
  for u in consumers do
    if clNew.contains u then throwError "SRM8 AUDIT FAILED: design_at_free_h routes through the uniform consumer {u}"
  let bad := (clNew.toList.filter fun c => forbidden.any (·.isPrefixOf c))
  unless bad.isEmpty do throwError "SRM8 AUDIT FAILED: old-form boundary in the closure of design_at_free_h: {bad}"
  -- the bridge is a DEFINITION (a Prop to be assumed), not a theorem, and design_at_free_h takes it as a binder
  match (← getEnv).find? ``Tools.ShippingSrm8Bridge.HeightBridge with
  | some (.defnInfo _) => pure ()
  | _ => throwError "SRM8 AUDIT FAILED: HeightBridge is not a definition"
  let hb ← premiseRows ``Tools.ShippingSrm8Bridge.design_at_free_h
  unless hb.any (fun r => r.2.2.1 == "hbridge" && r.2.2.2.1 && (r.2.2.2.2.splitOn "HeightBridge").length > 1) do
    throwError "SRM8 AUDIT FAILED: design_at_free_h has no Prop binder hbridge : HeightBridge _"
  for thm in audited8 do
    stdAxioms thm
    logInfo m!"S8CLOSURE|{thm}|standard axioms"
  logInfo m!"S8CLOSURE-NEW|design_at_free_h: closure {clNew.size} constants; no uniform consumer; no old-form boundary; HeightBridge a def taken as binder hbridge"

end
