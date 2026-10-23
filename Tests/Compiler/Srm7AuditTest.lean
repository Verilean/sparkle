import Tests.Compiler.Srm7RankTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm7AuditExpected
import Tools.ShippingKidsChildIfaceM
-- BUILT (unit SRM7B): fixture 1 made semantic (` ∧ True`); see REPORT-SRM7B.md for runs.  History: SRM7 dev run s7c2 exit 0.
-- SCOPE (SRM7, audits; copied from `Srm5AuditTest`, SRM5 files untouched).  For each audited SRM7 theorem: (1) PREMISE TABLE: every binder (index, binderInfo, name, Prop-or-data, type) is printed as an `S7PREM` / `S7DATA` line
-- and the WHOLE table must EQUAL the committed `Tests/Compiler/Srm7AuditExpected.lean` (`expectedRows`) EXACTLY and `scripts/srm7/PREMISES.txt`, line for line.  LITERAL guards: `audited7.length == 40`, `expectedRows.length == 40`.
-- NEGATIVE FIXTURES: three mutations of the actual table (changed Prop binder type, added data binder, reordered binders) are REJECTED by the comparator and are non-vacuous (`S7FIXTURE`).
-- REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm7AuditTest > LOG 2>&1; python3 scripts/srm7/gen_audit.py LOG` (a stale expected file makes the first build fail AFTER printing the rows).
-- (2) BINDER AUDIT: no hypothesis restates the conclusion (control: a hand-made wrapper IS caught).  (3) CLOSURE AUDIT: standard axioms only, no old-form constant in the closure (forbidden roots exist; control: the old-form `kidsChild_of_realM` is caught).
-- (4) the two instances with COMPUTED ranks have no rank-table binder (`rk`, `hrkmem`, `hrT`, ...) and their closure contains `declRank` and `hcheck`.  (5) each listed rank fact has the corresponding `machineData` constant and `instTagged` in its closure (the graph is READ, not typed in).
-- NOT guaranteed: truth/satisfiability of the remaining hypotheses (`O`, `T`, `hA`, `MachineDefines`, `hcore`, `hpost`, `hw`); type strings are `ppExpr` renderings.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm7AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited7 SRM7 theorems -/
def audited7 : List Name :=
  [``Tools.ShippingSrm7Rank.kidsMax_le, ``Tools.ShippingSrm7Rank.kidsMax_mono, ``Tools.ShippingSrm7Rank.kidsMax_lt, ``Tools.ShippingSrm7Rank.declRank_mono,
   ``Tools.ShippingSrm7Rank.declRank_le, ``Tools.ShippingSrm7Rank.rkOf_mem, ``Tools.ShippingSrm7Rank.rkOf_decl, ``Tools.ShippingSrm7Rank.rkOf_edge,
   ``Tools.ShippingSrm7Rank.rank_pos, ``Tools.ShippingSrm7Rank.declRank_self, ``Tools.ShippingSrm7Rank.rkChecked_dup, ``Tools.ShippingSrm7Rank.rkChecked_wf,
   ``Tools.ShippingSrm7Rank.inClass_rank,
   ``Tests.Compiler.Srm7RankTest.gM_inClass, ``Tests.Compiler.Srm7RankTest.gM_top, ``Tests.Compiler.Srm7RankTest.gM_wrap, ``Tests.Compiler.Srm7RankTest.gM_wrap3,
   ``Tests.Compiler.Srm7RankTest.gM_leaf, ``Tests.Compiler.Srm7RankTest.gQ_inClass, ``Tests.Compiler.Srm7RankTest.gQ_top, ``Tests.Compiler.Srm7RankTest.gQ_wrapP,
   ``Tests.Compiler.Srm7RankTest.gQ_wrapQ, ``Tests.Compiler.Srm7RankTest.gQ_leaf,
   ``Tests.Compiler.Srm7RankTest.rkOf_gM_eq_rkM, ``Tests.Compiler.Srm7RankTest.rkOf_gQ_eq_rkQ,
   ``Tests.Compiler.Srm7RankTest.topshareM_hcheck_computed, ``Tests.Compiler.Srm7RankTest.topshareQ_hcheck_computed,
   ``Tests.Compiler.Srm7RankTest.gTwo_inClass, ``Tests.Compiler.Srm7RankTest.gTwo_top, ``Tests.Compiler.Srm7RankTest.gColl_refused, ``Tests.Compiler.Srm7RankTest.gColl_notInClass,
   ``Tests.Compiler.Srm7RankTest.okG_rank, ``Tests.Compiler.Srm7RankTest.cycG_refused, ``Tests.Compiler.Srm7RankTest.selfG_refused, ``Tests.Compiler.Srm7RankTest.missG_refused,
   ``Tests.Compiler.Srm7RankTest.dupG_wf, ``Tests.Compiler.Srm7RankTest.dupG_class, ``Tests.Compiler.Srm7RankTest.dupG_table, ``Tests.Compiler.Srm7RankTest.okG_fuel,
   ``Tests.Compiler.Srm7RankTest.gMnoLeaf_refused]

/-- the instances whose rank premises are replaced by the computation: no rank-table binder may remain -/
def computedThms : List Name :=
  [``Tests.Compiler.Srm7RankTest.topshareM_hcheck_computed, ``Tests.Compiler.Srm7RankTest.topshareQ_hcheck_computed]

/-- the rank facts whose graph must be READ from the machine data -/
def readThms : List (Name × Name) :=
  [(``Tests.Compiler.Srm7RankTest.gM_top, ``Tests.Compiler.SharedLeafMemKidTest.topshareM.machineData),
   (``Tests.Compiler.Srm7RankTest.gM_leaf, ``Tests.Compiler.SharedLeafMemKidTest.leafM.machineData),
   (``Tests.Compiler.Srm7RankTest.gQ_top, ``Tests.Compiler.SharedLeafMemKidTest.topshareQ.machineData),
   (``Tests.Compiler.Srm7RankTest.gTwo_top, ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData),
   (``Tests.Compiler.Srm7RankTest.gColl_refused, ``Sparkle.Tests.Compiler.NonzeroInitParentTest.collMixSame5.machineData)]

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

/-- the text line of a row (the format of `scripts/srm7/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S7{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

/-- EXACT comparison of two whole tables: `none` iff equal, else the first difference -/
def tableDiff (a e : List (Name × List Row)) : Option String := Id.run do
  if a.length != e.length then return some s!"{a.length} theorems vs {e.length} expected"
  for ((n, rs), (n', rs')) in a.zip e do
    if n != n' then return some s!"theorem {n} vs expected {n'}"
    if rs.length != rs'.length then return some s!"{n}: {rs.length} binders vs {rs'.length} expected"
    for (r, r') in rs.zip rs' do
      if r != r' then return some s!"{n}: binder {r.1} differs: {rowLine n r} vs expected {rowLine n r'}"
  return none

/-- mutation 1: SEMANTIC change of the type of the first Prop binder (same index, binderInfo, name, isProp): ` ∧ True` is appended to its type string -/
def mutType (t : List (Name × List Row)) : List (Name × List Row) :=
  match t.findIdx? (fun (_, rs) => rs.any (·.2.2.2.1)) with
  | none => t
  | some k => t.mapIdx fun j (n, rs) =>
    if j == k then
      let idx := (rs.findIdx? (·.2.2.2.1)).getD 0
      (n, rs.mapIdx fun i r => if i == idx then (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2 ++ " ∧ True") else r)
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
      if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingDesignSV.kidsPass || c == ``Tools.ShippingChecksDesign.kidCheck) then return true
    return false

end Tests.Compiler.Srm7AuditTest

open Tests.Compiler.Srm7AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm7AuditTest.wrapper_mutation) do throwError "SRM7 AUDIT FAILED: the wrapper control was not caught"
  -- LITERAL fixed-count guard, independent of the generated expected file
  unless audited7.length == 40 do throwError "SRM7 AUDIT FAILED: audited7 has {audited7.length} theorems, expected exactly 40"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited7 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S7THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S7THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM7 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  unless Tests.Compiler.Srm7AuditExpected.expectedRows.length == 40 do throwError "SRM7 AUDIT FAILED: the expected table has {Tests.Compiler.Srm7AuditExpected.expectedRows.length} theorem entries, expected exactly 40"
  -- the whole table equals the committed expected table, EXACTLY
  match tableDiff actual Tests.Compiler.Srm7AuditExpected.expectedRows with
  | some msg => throwError "SRM7 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm7AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm7/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM7 AUDIT FAILED: scripts/srm7/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  -- FIXTURE 1 assertions: a visible semantic change of ONE Prop binder, everything else unchanged, rejected naming that binder
  do
    let mt := mutType actual
    let some k := actual.findIdx? (fun (_, rs) => rs.any (·.2.2.2.1)) | throwError "SRM7 AUDIT FAILED: no Prop binder to mutate"
    let (thm, rs) := actual[k]!
    let idx := (rs.findIdx? (·.2.2.2.1)).getD 0
    let r := rs[idx]!
    let (thm', rs') := mt[k]!
    let r' := rs'[idx]!
    unless thm' == thm && rs'.length == rs.length do throwError "SRM7 AUDIT FAILED: fixture 1 changed the shape of {thm}"
    if r'.2.2.2.2 == r.2.2.2.2 then throwError "SRM7 AUDIT FAILED: fixture 1 type string is not different"
    unless r'.2.2.2.2 == r.2.2.2.2 ++ " ∧ True" do throwError "SRM7 AUDIT FAILED: fixture 1 is not the visible ` ∧ True` change"
    unless r'.2.2.2.1 == true && r'.1 == r.1 && r'.2.1 == r.2.1 && r'.2.2.1 == r.2.2.1 do throwError "SRM7 AUDIT FAILED: fixture 1 mutated row is not a Prop binder with unchanged index/binderInfo/name"
    for ((n, rows), j) in actual.zipIdx do
      for (row, i) in rows.zipIdx do
        unless (j == k && i == idx) || mt[j]!.2[i]! == row do throwError "SRM7 AUDIT FAILED: fixture 1 changed another row ({n}, binder {i})"
    unless mt.length == actual.length && (mt.map (·.1)) == (actual.map (·.1)) do throwError "SRM7 AUDIT FAILED: fixture 1 changed the theorem list"
    match tableDiff mt Tests.Compiler.Srm7AuditExpected.expectedRows with
    | none => throwError "SRM7 AUDIT FAILED: the comparator ACCEPTED fixture 1"
    | some msg =>
      unless (msg.splitOn s!"{thm}: binder {idx} differs").length > 1 do throwError "SRM7 AUDIT FAILED: the comparator did not name the mutated binder ({thm}, {idx}): {msg}"
    logInfo m!"S7FIXTURE1|original: {rowLine thm r}"
    logInfo m!"S7FIXTURE1|mutated:  {rowLine thm r'}"
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM7 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm7AuditExpected.expectedRows with
    | none => throwError "SRM7 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S7FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S7TABLE|{audited7.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm7/PREMISES.txt"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM7 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM7 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited7 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM7 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM7 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    stdAxioms thm
    logInfo m!"S7CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary"
  -- (4) the instances with COMPUTED ranks: no rank-table binder remains, and the closure uses the computation and `hcheck`
  for thm in computedThms do
    let rows ← premiseRows thm
    for r in rows do
      let nm := r.2.2.1
      if ["rk", "hrkmem", "hrT", "hrW", "hrW3", "hrL", "hrP", "hrQ"].contains nm then
        throwError "SRM7 AUDIT FAILED: {thm} still has the rank-table binder {nm}"
    let cl ← depClosure thm
    unless cl.contains ``Tools.ShippingSrm7Rank.declRank do throwError "SRM7 AUDIT FAILED: the computation is not in the closure of {thm}"
    unless cl.contains ``Tools.ShippingSrm5Height.hcheck do throwError "SRM7 AUDIT FAILED: hcheck is not in the closure of {thm}"
  -- (5) the graphs are READ from the generated machine data (the machineData constant is in the closure of the rank fact)
  for (thm, md) in readThms do
    let cl ← depClosure thm
    unless cl.contains md do throwError "SRM7 AUDIT FAILED: the closure of {thm} does not contain {md} (graph not read from the machine data)"
    unless cl.contains ``Sparkle.Compiler.Elab.MachineShape.instTagged do throwError "SRM7 AUDIT FAILED: the closure of {thm} does not contain instTagged"
  logInfo m!"S7READ|{readThms.length} rank facts read their graph from machineData"

end
