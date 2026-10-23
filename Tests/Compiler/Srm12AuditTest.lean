import Tests.Compiler.Srm12CorrTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm12AuditExpected
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingSrm12Corr
-- BUILT (unit SRM12): dev runs a5 (Corr + CorrTest) exit 0, a8 (audit) exit 0; the final-SHA rebuild is in REPORT-SRM12.md.
-- SCOPE (SRM12, audits).  For each audited SRM12 theorem (Tools/ShippingSrm12Corr.lean and Tests/Compiler/Srm12CorrTest.lean): (1) PREMISE TABLE: every binder (index, binderInfo, name, Prop-or-data, type) is printed as an `S12PREM` / `S12DATA` line and the WHOLE
-- table must EQUAL the committed `Tests/Compiler/Srm12AuditExpected.lean` (`expectedRows`) EXACTLY and the committed text view `scripts/srm12/PREMISES.txt`, line for line; one `S12THM` marker line per theorem (zero-binder theorems kept).
-- NEGATIVE FIXTURES: three mutations of the actual table (SEMANTIC Prop type change ` ∧ True`, added data binder, reordered binders) are REJECTED, each asserted non-vacuous.  REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm12AuditTest > LOG 2>&1; python3 scripts/srm12/gen_audit.py LOG`.
-- (2) BINDER AUDIT: no hypothesis restates the conclusion (control: a hand-made wrapper IS caught).  (3) CLOSURE AUDIT: standard axioms only, no old `RefLaws`/`RealChild`/`InvW`/`MachineRan`/`MachineClosesAt`/`ChildBnd`/`KidFacts`-form constant in the closure (every forbidden root exists; the old-form `kidsChild_of_realM` IS caught by the same walk).
-- The instances `topshareM_corr`/`topshareQ_corr` use `ran_designCorr`; the rank consequences use SRM7's `rkOf_edge`.  NOT guaranteed: that the hypotheses are TRUE in general; type strings are `ppExpr` renderings.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm12AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited SRM12 theorems -/
def audited12 : List Name :=
  [``Tools.ShippingSrm12Corr.decode_ofMem,
   ``Tools.ShippingSrm12Corr.decode_ofDecl,
   ``Tools.ShippingSrm12Corr.kidModName_mem_iff,
   ``Tools.ShippingSrm12Corr.decode_kidModName,
   ``Tools.ShippingSrm12Corr.kidTA_name,
   ``Tools.ShippingSrm12Corr.instTagged_mem_idx,
   ``Tools.ShippingSrm12Corr.instTagged_exists_idx,
   ``Tools.ShippingSrm12Corr.memModule_modCorr,
   ``Tools.ShippingSrm12Corr.memModule_design_modules,
   ``Tools.ShippingSrm12Corr.ran_instFwd,
   ``Tools.ShippingSrm12Corr.ran_instBwd,
   ``Tools.ShippingSrm12Corr.modCorr_of_run,
   ``Tools.ShippingSrm12Corr.ran_designCorr,
   ``Tools.ShippingSrm12Corr.memCallee_childCorr,
   ``Tools.ShippingSrm12Corr.childCorr_noInst,
   ``Tools.ShippingSrm12Corr.callees_mem_names,
   ``Tools.ShippingSrm12Corr.inst_rank,
   ``Tests.Compiler.Srm12CorrTest.gM_top_callees,
   ``Tests.Compiler.Srm12CorrTest.gM_wrap_callees,
   ``Tests.Compiler.Srm12CorrTest.gM_wrap3_callees,
   ``Tests.Compiler.Srm12CorrTest.gM_leaf_callees,
   ``Tests.Compiler.Srm12CorrTest.gQ_top_callees,
   ``Tests.Compiler.Srm12CorrTest.gQ_wrapP_callees,
   ``Tests.Compiler.Srm12CorrTest.gQ_wrapQ_callees,
   ``Tests.Compiler.Srm12CorrTest.gQ_leaf_callees,
   ``Tests.Compiler.Srm12CorrTest.leafM_childCorr,
   ``Tests.Compiler.Srm12CorrTest.wrapM_childCorr,
   ``Tests.Compiler.Srm12CorrTest.wrapM3_childCorr,
   ``Tests.Compiler.Srm12CorrTest.topshareM_corr,
   ``Tests.Compiler.Srm12CorrTest.leafP_childCorr,
   ``Tests.Compiler.Srm12CorrTest.wrapP_childCorr,
   ``Tests.Compiler.Srm12CorrTest.wrapQ_childCorr,
   ``Tests.Compiler.Srm12CorrTest.topshareQ_corr,
   ``Tests.Compiler.Srm12CorrTest.gM_names,
   ``Tests.Compiler.Srm12CorrTest.gQ_names,
   ``Tests.Compiler.Srm12CorrTest.gM_rank_of_modCorr,
   ``Tests.Compiler.Srm12CorrTest.gQ_rank_of_modCorr,
   ``Tests.Compiler.Srm12CorrTest.inst_rank_of_modCorr_M,
   ``Tests.Compiler.Srm12CorrTest.inst_rank_of_modCorr_Q,
   ``Tests.Compiler.Srm12CorrTest.topshareM_inst_ranks,
   ``Tests.Compiler.Srm12CorrTest.topshareQ_inst_ranks]

/-- the INSTANCE theorems (per design) -/
def instanceThms : List Name :=
  [``Tests.Compiler.Srm12CorrTest.topshareM_corr, ``Tests.Compiler.Srm12CorrTest.topshareQ_corr, ``Tests.Compiler.Srm12CorrTest.topshareM_inst_ranks, ``Tests.Compiler.Srm12CorrTest.topshareQ_inst_ranks]


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

/-- the text line of a row (the format of `scripts/srm12/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S12{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

/-- EXACT comparison of two whole tables: `none` iff equal, else the first difference -/
def tableDiff (a e : List (Name × List Row)) : Option String := Id.run do
  if a.length != e.length then return some s!"{a.length} theorems vs {e.length} expected"
  for ((n, rs), (n', rs')) in a.zip e do
    if n != n' then return some s!"theorem {n} vs expected {n'}"
    if rs.length != rs'.length then return some s!"{n}: {rs.length} binders vs {rs'.length} expected"
    for (r, r') in rs.zip rs' do
      if r != r' then return some s!"{n}: binder {r.1} differs: {rowLine n r} vs expected {rowLine n r'}"
  return none

/-- mutation 1: SEMANTIC change of the type of the first Prop binder (same index, binderInfo, name): the type string gets ` ∧ True` appended -/
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

end Tests.Compiler.Srm12AuditTest

open Tests.Compiler.Srm12AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm12AuditTest.wrapper_mutation) do throwError "SRM12 AUDIT FAILED: the wrapper control was not caught"
  -- LITERAL fixed-count guard, independent of the generated expected file
  unless audited12.length == 41 do throwError "SRM12 AUDIT FAILED: audited12 has {audited12.length} theorems, expected exactly 41"
  unless Tests.Compiler.Srm12AuditExpected.expectedRows.length == 41 do throwError "SRM12 AUDIT FAILED: the expected table has {Tests.Compiler.Srm12AuditExpected.expectedRows.length} theorem entries, expected exactly 41"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited12 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S12THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S12THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM12 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  -- the whole table equals the committed expected table, EXACTLY
  match tableDiff actual Tests.Compiler.Srm12AuditExpected.expectedRows with
  | some msg => throwError "SRM12 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm12AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm12/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM12 AUDIT FAILED: scripts/srm12/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  -- fixture 1 is SEMANTIC: exactly one row differs, it is still a Prop binder with the same index/binderInfo/name, and its type string visibly differs
  do
    let mt := mutType actual
    let mut changed : List (Name × Row × Row) := []
    unless mt.length == actual.length do throwError "SRM12 AUDIT FAILED: fixture 1 changed the number of theorems"
    for ((n, rs), (n', rs')) in actual.zip mt do
      unless n == n' && rs.length == rs'.length do throwError "SRM12 AUDIT FAILED: fixture 1 changed the shape of {n}"
      for (r, r') in rs.zip rs' do
        if r != r' then changed := changed ++ [(n, r, r')]
    match changed with
    | [(n, r, r')] =>
      unless r'.2.2.2.1 do throwError "SRM12 AUDIT FAILED: fixture 1 mutated row of {n} is not a Prop binder"
      unless r.2.2.2.1 && r'.1 == r.1 && r'.2.1 == r.2.1 && r'.2.2.1 == r.2.2.1 do throwError "SRM12 AUDIT FAILED: fixture 1 changed index/binderInfo/name/isProp of binder {r.1} of {n}"
      unless r'.2.2.2.2 != r.2.2.2.2 && r'.2.2.2.2.endsWith " ∧ True" && r'.2.2.2.2.length == r.2.2.2.2.length + 7 do throwError "SRM12 AUDIT FAILED: fixture 1 type string is not visibly changed"
      logInfo m!"S12FIXTURE1|{n}|binder {r.1} ({r.2.2.1})|original type: {r.2.2.2.2}|mutated type: {r'.2.2.2.2}"
      match tableDiff mt Tests.Compiler.Srm12AuditExpected.expectedRows with
      | some msg => unless (msg.splitOn s!"binder {r.1} differs").length > 1 && (msg.splitOn (toString n)).length > 1 do throwError "SRM12 AUDIT FAILED: fixture 1 rejection does not name the mutated binder: {msg}"
      | none => throwError "SRM12 AUDIT FAILED: the comparator ACCEPTED fixture 1"
    | _ => throwError "SRM12 AUDIT FAILED: fixture 1 changed {changed.length} rows, expected exactly 1"
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM12 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm12AuditExpected.expectedRows with
    | none => throwError "SRM12 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S12FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S12TABLE|{audited12.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm12/PREMISES.txt"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM12 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM12 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited12 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM12 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM12 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    if instanceThms.contains thm then
      unless cl.contains ``Tools.ShippingSrm12Corr.ran_designCorr || thm == ``Tests.Compiler.Srm12CorrTest.topshareM_inst_ranks || thm == ``Tests.Compiler.Srm12CorrTest.topshareQ_inst_ranks do throwError "SRM12 AUDIT FAILED: ran_designCorr not in the closure of {thm}"
    if thm == ``Tests.Compiler.Srm12CorrTest.topshareM_inst_ranks || thm == ``Tests.Compiler.Srm12CorrTest.topshareQ_inst_ranks || thm == ``Tools.ShippingSrm12Corr.inst_rank then
      unless cl.contains ``Tools.ShippingSrm7Rank.rkOf_edge do throwError "SRM12 AUDIT FAILED: SRM7 rkOf_edge not in the closure of {thm}"
    if thm == ``Tests.Compiler.Srm12CorrTest.topshareM_corr || thm == ``Tests.Compiler.Srm12CorrTest.topshareQ_corr then
      unless cl.contains ``Tools.ShippingSrm5Ident.inst_target_ranA do throwError "SRM12 AUDIT FAILED: inst_target_ranA not in the closure of {thm}"
      unless cl.contains ``Tools.ShippingMachineInstG.closeInstsG_calls do throwError "SRM12 AUDIT FAILED: closeInstsG_calls not in the closure of {thm}"
    stdAxioms thm
    logInfo m!"S12CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary"

end
