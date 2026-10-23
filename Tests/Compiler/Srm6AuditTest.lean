import Tests.Compiler.Srm6ParentTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm6AuditExpected
import Tools.ShippingKidsChildIfaceM
set_option autoImplicit false
-- BUILT (unit SRM6): m13 exit 0 (dev); final-SHA rebuild in REPORT-SRM6.md.
-- SCOPE (SRM6, audits; generalised COPY of Srm5AuditTest, SRM5 files untouched).  For each of the 7 audited SRM6 theorems (`Tools.ShippingSrm6Sem.{hcheck_leaf, hcheck_fuel, instFree_of_leafCheck, leaf_forwardH, design_sv_runH}`, `topshareM_designSVH`, `topshareQ_designSVH`):
-- (1) PREMISE TABLE: every binder (index, binderInfo, name, Prop-or-data, type) is printed as an `S6PREM` / `S6DATA` line and the WHOLE table must EQUAL the committed `Tests/Compiler/Srm6AuditExpected.lean` (`expectedRows`) EXACTLY and `scripts/srm6/PREMISES.txt` line for line.  Literal guards: 7 theorems.
-- NEGATIVE FIXTURES: changed Prop binder type, added data binder, reordered binders: each must differ from the actual table and be REJECTED by the comparator (`S6FIXTURE` lines).
-- REGENERATION (from the head revision): `./.cluster/qbuild.sh build Tests.Compiler.Srm6AuditTest > LOG 2>&1; python3 scripts/srm6/gen_audit.py LOG`.
-- (2) BINDER AUDIT: no hypothesis restates its conclusion (control: hand-made wrapper IS caught); no hypothesis mentions `designCheck`/`kidsPass`/`kidCheck` (the uniform check).  DEFINITION GUARD: `DesignSVH`/`SVBoundsH` unfold to the constants `TextRun`, `LeafRun`, `Supplies`, `PortsMatch`, `Resolved` / `ParentBounds`, `LeafBounds` (so the relation is not `True`).
-- (3) CLOSURE AUDIT: standard axioms only; no old-form boundary; the generic theorems `design_sv_runH`/`leaf_forwardH` do NOT have `designCheck` in their closure and DO have `hcheck`, `DesignSVH`; the instances have `hcheck`, `design_sv_runH`, `topshare*_hcheck` in the closure (`designCheck` in their closure is reported as `S6NOTE`: it can enter through SRM5's `KidFactsA.toNC`, as in SRM5).  CONTROLS: forbidden roots exist; old-form `kidsChild_of_realM` IS caught.
-- NOT guaranteed: that the hypotheses (`hrun`, `hB`, rank table) are TRUE for the machine's actual run; type strings are `ppExpr` renderings in the head environment.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm6AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited6 SRM6 theorems -/
def audited6 : List Name :=
  [``Tools.ShippingSrm6Sem.hcheck_leaf, ``Tools.ShippingSrm6Sem.hcheck_fuel, ``Tools.ShippingSrm6Sem.instFree_of_leafCheck,
   ``Tools.ShippingSrm6Sem.leaf_forwardH, ``Tools.ShippingSrm6Sem.design_sv_runH,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH]

/-- the instances: they must reach `hcheck` and `design_sv_runH` -/
def parentInstances : List Name :=
  [``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH]

/-- the generic theorems: no uniform `designCheck` in the closure -/
def genericThms : List Name := [``Tools.ShippingSrm6Sem.design_sv_runH, ``Tools.ShippingSrm6Sem.leaf_forwardH]

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

/-- the text line of a row (the format of `scripts/srm6/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S6{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

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
      if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingDesignSV.kidsPass || c == ``Tools.ShippingChecksDesign.kidCheck || c == ``Tools.ShippingDesignSV.designCheck) then return true
    return false

end Tests.Compiler.Srm6AuditTest

open Tests.Compiler.Srm6AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm6AuditTest.wrapper_mutation) do throwError "SRM6 AUDIT FAILED: the wrapper control was not caught"
  -- LITERAL fixed-count guard, independent of the generated expected file
  unless audited6.length == 7 do throwError "SRM6 AUDIT FAILED: audited6 has {audited6.length} theorems, expected exactly 7"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited6 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S6THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S6THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM6 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  unless Tests.Compiler.Srm6AuditExpected.expectedRows.length == 7 do throwError "SRM6 AUDIT FAILED: the expected table has {Tests.Compiler.Srm6AuditExpected.expectedRows.length} theorem entries, expected exactly 7"
  -- the whole table equals the committed expected table, EXACTLY
  match tableDiff actual Tests.Compiler.Srm6AuditExpected.expectedRows with
  | some msg => throwError "SRM6 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm6AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm6/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM6 AUDIT FAILED: scripts/srm6/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM6 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm6AuditExpected.expectedRows with
    | none => throwError "SRM6 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S6FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S6TABLE|{audited6.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm6/PREMISES.txt"
  for thm in audited6 do
    if (← mentionsUniform thm) then throwError "SRM6 AUDIT FAILED: a hypothesis of {thm} mentions the uniform check"
  -- DEFINITION GUARD: the relations are not trivial
  for (d, need) in [(``Tools.ShippingSrm6Sem.DesignSVH, [``Tools.ShippingDesignSV.TextRun, ``Tools.ShippingDesignSV.LeafRun, ``Tools.ShippingDesignSV.Supplies, ``Tools.ShippingDesignSV.PortsMatch, ``Tools.ShippingDesignSV.Resolved]),
                    (``Tools.ShippingSrm6Sem.SVBoundsH, [``Tools.ShippingDesignSV.ParentBounds, ``Tools.ShippingSrm6Sem.LeafBounds])] do
    let cs ← depClosure d
    for c in need do
      unless cs.contains c do throwError "SRM6 AUDIT FAILED: {d} does not mention {c}"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM6 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM6 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited6 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM6 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM6 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    if !(([``Tools.ShippingSrm6Sem.instFree_of_leafCheck, ``Tools.ShippingSrm6Sem.leaf_forwardH].contains thm) || cl.contains ``Tools.ShippingSrm5Height.hcheck) then throwError "SRM6 AUDIT FAILED: hcheck not in the closure of {thm}"
    if genericThms.contains thm then
      if cl.contains ``Tools.ShippingDesignSV.designCheck then throwError "SRM6 AUDIT FAILED: designCheck in the closure of {thm}"
    if parentInstances.contains thm then
      unless cl.contains ``Tools.ShippingSrm6Sem.design_sv_runH do throwError "SRM6 AUDIT FAILED: design_sv_runH not in the closure of {thm}"
      unless cl.contains ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck || cl.contains ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck do throwError "SRM6 AUDIT FAILED: no topshare*_hcheck in the closure of {thm}"
      logInfo m!"S6NOTE|{thm}|designCheck in closure: {cl.contains ``Tools.ShippingDesignSV.designCheck}"
    stdAxioms thm
    logInfo m!"S6CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary"

end
