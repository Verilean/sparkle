import Tests.Compiler.Srm10OutsTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm10AuditExpected
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingSrm10Outs
-- BUILT/UNBUILT: UNBUILT (unit SRM10; build runs are listed in REPORT-SRM10.md).
-- SCOPE (SRM10, audits).  For each audited SRM10 theorem: (1) PREMISE TABLE: every binder (index, binderInfo, name, Prop-or-data, type) is printed as an `S10PREM` / `S10DATA` line and the WHOLE table must EQUAL the committed
-- `Tests/Compiler/Srm10AuditExpected.lean` (`expectedRows`) EXACTLY and the committed text view `scripts/srm10/PREMISES.txt`, line for line.  NEGATIVE FIXTURES: three mutations of the actual table (changed Prop binder type, added data binder,
-- reordered binders) are REJECTED.  REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm10AuditTest > LOG 2>&1; python3 scripts/srm10/gen_audit.py LOG`.  Binder names containing `_hyg` are normalised to `_anon`.
-- (2) BINDER AUDIT: no hypothesis restates the conclusion (control: a hand-made wrapper IS caught); the two topshare instances have NO hypothesis mentioning `outsCheck`/`kidsPass`/`designCheck`/`kidCheck` (their only inputs are the SRM4/SRM5 premises).
-- (3) CLOSURE AUDIT: standard axioms only, no old `RefLaws`/`RealChild`/`InvW`/`MachineRan`/`MachineClosesAt`/`ChildBnd`/`KidFacts`-form constant in the closure (every forbidden root exists; the old-form `kidsChild_of_realM` IS caught by the same walk);
-- `houtsCheck` is in the closure of the link theorems and the instances; the instances use `hcheck` (SRM5) and SRM4's `outsCheck` supply.  NOT guaranteed: that the hypotheses are TRUE in general; type strings are `ppExpr` renderings.
set_option Elab.async false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm10AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited10 SRM10 theorems -/
def audited10 : List Name :=
  [``Tools.ShippingSrm10Outs.outsLeaf_of_outsAssigned,
   ``Tools.ShippingSrm10Outs.houtsMod_rank0,
   ``Tools.ShippingSrm10Outs.houtsMod_succ_iff,
   ``Tools.ShippingSrm10Outs.houtsMod_pos,
   ``Tools.ShippingSrm10Outs.houtsMod_outs,
   ``Tools.ShippingSrm10Outs.houtsCheck_at,
   ``Tools.ShippingSrm10Outs.kidsPass_of_resolved,
   ``Tools.ShippingSrm10Outs.outsCheck_succ_at,
   ``Tools.ShippingSrm10Outs.outsCheck_of_houtsCheck_uni,
   ``Tools.ShippingSrm10Outs.houtsMod_of_outsCheck_hcheck,
   ``Tools.ShippingSrm10Outs.houtsCheck_of_outsCheck_hcheck,
   ``Tools.ShippingSrm10Outs.houtsMod_norank,
   ``Tools.ShippingSrm10Outs.houtsCheck_unresolved,
   ``Tools.ShippingSrm10Outs.houtsCheck_notBelow,
   ``Tools.ShippingSrm10Outs.houtsMod_rank0_refused,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_houts,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_houts]

/-- the INSTANCE theorems: no hypothesis may mention the uniform checks -/
def instanceThms : List Name :=
  [``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_houts, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_houts]


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

/-- the text line of a row (the format of `scripts/srm10/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S10{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

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

/-- does a hypothesis of `thm` mention the uniform children's check? -/
def mentionsUniform (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingDesignSV.kidsPass || c == ``Tools.ShippingChecksDesign.kidCheck || c == ``Tools.ShippingDesignSVBack.outsCheck || c == ``Tools.ShippingDesignSV.designCheck) then return true
    return false

end Tests.Compiler.Srm10AuditTest

open Tests.Compiler.Srm10AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm10AuditTest.wrapper_mutation) do throwError "SRM10 AUDIT FAILED: the wrapper control was not caught"
  -- LITERAL fixed-count guard, independent of the generated expected file
  unless audited10.length == 17 do throwError "SRM10 AUDIT FAILED: audited10 has {audited10.length} theorems, expected exactly 17"
  unless Tests.Compiler.Srm10AuditExpected.expectedRows.length == 17 do throwError "SRM10 AUDIT FAILED: the expected table has {Tests.Compiler.Srm10AuditExpected.expectedRows.length} theorem entries, expected exactly 17"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited10 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S10THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S10THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM10 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  -- the whole table equals the committed expected table, EXACTLY
  match tableDiff actual Tests.Compiler.Srm10AuditExpected.expectedRows with
  | some msg => throwError "SRM10 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm10AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm10/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM10 AUDIT FAILED: scripts/srm10/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM10 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm10AuditExpected.expectedRows with
    | none => throwError "SRM10 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S10FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S10TABLE|{audited10.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm10/PREMISES.txt"
  for thm in instanceThms do
    if (← mentionsUniform thm) then throwError "SRM10 AUDIT FAILED: a hypothesis of {thm} mentions the uniform children's check"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM10 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM10 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited10 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM10 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM10 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    let s := thm.toString
    let has (x : String) : Bool := (s.splitOn x).length > 1
    if has "outsCheck_of_houtsCheck_uni" || has "_houts" || has "houtsCheck_of_outsCheck_hcheck" || has "houtsMod_of_outsCheck_hcheck" then
      unless cl.contains ``Tools.ShippingSrm10Outs.houtsMod do throwError "SRM10 AUDIT FAILED: houtsMod not in the closure of {thm}"
    if has "houtsCheck_of_outsCheck_hcheck" || has "houtsMod_of_outsCheck_hcheck" || has "_houts" then
      unless cl.contains ``Tools.ShippingSrm5Height.hcheck do throwError "SRM10 AUDIT FAILED: hcheck not in the closure of {thm}"
    if has "outsCheck_of_houtsCheck_uni" then
      unless cl.contains ``Tools.ShippingDesignSVBack.outsCheck do throwError "SRM10 AUDIT FAILED: outsCheck not in the closure of {thm}"
    if instanceThms.contains thm then
      unless cl.contains ``Tools.ShippingSrm10Outs.houtsCheck_of_outsCheck_hcheck do throwError "SRM10 AUDIT FAILED: link B not in the closure of {thm}"
      unless cl.contains ``Tools.ShippingDesignSVBack.outsCheck do throwError "SRM10 AUDIT FAILED: the SRM4 outsCheck supply is not in the closure of {thm} (it is used)"
    stdAxioms thm
    logInfo m!"S10CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary"

end
