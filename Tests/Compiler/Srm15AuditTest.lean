import Tests.Compiler.Srm15GraphTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm15AuditExpected
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingSrm15Graph
import Tools.ShippingSrm12Corr
import Tests.Compiler.Srm12CorrTest
import Tests.Compiler.Srm15ExpStmt
-- BUILT (unit SRM15): dev run s15e exit 0; the final-SHA rebuild is in REPORT-SRM15.md.
-- SCOPE (SRM15, audits).  For each audited SRM15 theorem (Tools/ShippingSrm15Graph.lean and Tests/Compiler/Srm15GraphTest.lean): (1) PREMISE TABLE: every binder (index, binderInfo, name, Prop-or-data, type) is printed as an `S15PREM` / `S15DATA` line and the WHOLE
-- table must EQUAL the committed `Tests/Compiler/Srm15AuditExpected.lean` (`expectedRows`) EXACTLY and the committed text view `scripts/srm15/PREMISES.txt`, line for line; one `S15THM` marker line per theorem (zero-binder theorems kept).
-- NEGATIVE FIXTURES: three mutations of the actual table (SEMANTIC Prop type change ` ∧ True`, added data binder, reordered binders) are REJECTED, each asserted non-vacuous.  REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm15AuditTest > LOG 2>&1; python3 scripts/srm15/gen_audit.py LOG`.
-- (2) BINDER AUDIT: no hypothesis restates the conclusion (control: a hand-made wrapper IS caught).  (3) CLOSURE AUDIT: standard axioms only, no old `RefLaws`/`RealChild`/`InvW`/`MachineRan`/`MachineClosesAt`/`ChildBnd`/`KidFacts`-form constant in the closure (every forbidden root exists; the old-form `kidsChild_of_realM` IS caught by the same walk).
-- The instances `topshareM_corr15`/`topshareQ_corr15` use `ran_designCorr_of_graphOf`; their statements are also checked isDefEq against the generated expected forms (Srm15ExpStmt) and against SRM12's `topshareM_corr`/`topshareQ_corr`.  NOT guaranteed: that the hypotheses are TRUE in general; type strings are `ppExpr` renderings.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm15AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited SRM15 theorems -/
def audited15 : List Name :=
  [``Tools.ShippingSrm15Graph.callees_graphOf,
   ``Tools.ShippingSrm15Graph.hname_of_iface,
   ``Tools.ShippingSrm15Graph.firstOcc_unique,
   ``Tools.ShippingSrm15Graph.ran_designCorr_of_graphOf,
   ``Tools.ShippingSrm15Graph.graphCovers_callees,
   ``Tests.Compiler.Srm15GraphTest.gM_eq_graphOf,
   ``Tests.Compiler.Srm15GraphTest.gQ_eq_graphOf,
   ``Tests.Compiler.Srm15GraphTest.dsM_top_first,
   ``Tests.Compiler.Srm15GraphTest.dsQ_top_first,
   ``Tests.Compiler.Srm15GraphTest.topshareM_corr15,
   ``Tests.Compiler.Srm15GraphTest.topshareQ_corr15]

/-- the INSTANCE theorems (per design) -/
def instanceThms : List Name :=
  [``Tests.Compiler.Srm15GraphTest.topshareM_corr15, ``Tests.Compiler.Srm15GraphTest.topshareQ_corr15]

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

/-- the text line of a row (the format of `scripts/srm15/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S15{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

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

end Tests.Compiler.Srm15AuditTest

open Tests.Compiler.Srm15AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm15AuditTest.wrapper_mutation) do throwError "SRM15 AUDIT FAILED: the wrapper control was not caught"
  -- LITERAL fixed-count guard, independent of the generated expected file
  unless audited15.length == 11 do throwError "SRM15 AUDIT FAILED: audited15 has {audited15.length} theorems, expected exactly 11"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited15 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S15THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S15THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM15 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  unless Tests.Compiler.Srm15AuditExpected.expectedRows.length == 11 do throwError "SRM15 AUDIT FAILED: the expected table has {Tests.Compiler.Srm15AuditExpected.expectedRows.length} theorem entries, expected exactly 11"
  -- the whole table equals the committed expected table, EXACTLY
  match tableDiff actual Tests.Compiler.Srm15AuditExpected.expectedRows with
  | some msg => throwError "SRM15 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm15AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm15/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM15 AUDIT FAILED: scripts/srm15/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  -- fixture 1 is SEMANTIC: exactly one row differs, it is still a Prop binder with the same index/binderInfo/name, and its type string visibly differs
  do
    let mt := mutType actual
    let mut changed : List (Name × Row × Row) := []
    unless mt.length == actual.length do throwError "SRM15 AUDIT FAILED: fixture 1 changed the number of theorems"
    for ((n, rs), (n', rs')) in actual.zip mt do
      unless n == n' && rs.length == rs'.length do throwError "SRM15 AUDIT FAILED: fixture 1 changed the shape of {n}"
      for (r, r') in rs.zip rs' do
        if r != r' then changed := changed ++ [(n, r, r')]
    match changed with
    | [(n, r, r')] =>
      unless r'.2.2.2.1 do throwError "SRM15 AUDIT FAILED: fixture 1 mutated row of {n} is not a Prop binder"
      unless r.2.2.2.1 && r'.1 == r.1 && r'.2.1 == r.2.1 && r'.2.2.1 == r.2.2.1 do throwError "SRM15 AUDIT FAILED: fixture 1 changed index/binderInfo/name/isProp of binder {r.1} of {n}"
      unless r'.2.2.2.2 != r.2.2.2.2 && r'.2.2.2.2.endsWith " ∧ True" && r'.2.2.2.2.length == r.2.2.2.2.length + 7 do throwError "SRM15 AUDIT FAILED: fixture 1 type string is not visibly changed"
      logInfo m!"S15FIXTURE1|{n}|binder {r.1} ({r.2.2.1})|original type: {r.2.2.2.2}|mutated type: {r'.2.2.2.2}"
      match tableDiff mt Tests.Compiler.Srm15AuditExpected.expectedRows with
      | some msg => unless (msg.splitOn s!"binder {r.1} differs").length > 1 && (msg.splitOn (toString n)).length > 1 do throwError "SRM15 AUDIT FAILED: fixture 1 rejection does not name the mutated binder: {msg}"
      | none => throwError "SRM15 AUDIT FAILED: the comparator ACCEPTED fixture 1"
    | _ => throwError "SRM15 AUDIT FAILED: fixture 1 changed {changed.length} rows, expected exactly 1"
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM15 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm15AuditExpected.expectedRows with
    | none => throwError "SRM15 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S15FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S15TABLE|{audited15.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm15/PREMISES.txt"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM15 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM15 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited15 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM15 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM15 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    if instanceThms.contains thm then
      unless cl.contains ``Tools.ShippingSrm15Graph.ran_designCorr_of_graphOf && cl.contains ``Tools.ShippingSrm12Corr.ran_designCorr do throwError "SRM15 AUDIT FAILED: ran_designCorr_of_graphOf/ran_designCorr not in the closure of {thm}"
    if thm == ``Tools.ShippingSrm15Graph.ran_designCorr_of_graphOf then
      unless cl.contains ``Tools.ShippingSrm15Graph.callees_graphOf && cl.contains ``Tools.ShippingSrm15Graph.hname_of_iface do throwError "SRM15 AUDIT FAILED: callees_graphOf/hname_of_iface not in the closure of {thm}"
    stdAxioms thm
    logInfo m!"S15CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary"


-- (4) INDEPENDENT EXPECTED STATEMENTS: `Tests/Compiler/Srm15ExpStmt.lean` is GENERATED by scripts/srm15/gen_exp.py from the SRM12 SOURCE statements only
-- (explicit substitution/deletion list, printed by the script); each audited statement is `isDefEq` to its expected form, and a deliberately wrong form (hkids deleted) is rejected.
run_cmd liftTermElabM do
  let pairs : List (Name × Name) :=
    [(``Tools.ShippingSrm15Graph.ran_designCorr_of_graphOf, ``Tests.Compiler.Srm15ExpStmt.Exp_ran_designCorr_of_graphOf),
     (``Tests.Compiler.Srm15GraphTest.topshareM_corr15, ``Tests.Compiler.Srm15ExpStmt.Exp_topshareM_corr15),
     (``Tests.Compiler.Srm15GraphTest.topshareQ_corr15, ``Tests.Compiler.Srm15ExpStmt.Exp_topshareQ_corr15)]
  for (t, e) in pairs do
    let ci ← getConstInfo t
    let ei ← getConstInfo e
    unless (← isDefEq ci.type (ei.value?.getD (mkConst e))) do throwError "SRM15 AUDIT FAILED: the statement of {t} is not defeq to its expected form {e}"
    logInfo m!"S15EXPDEFEQ|{t}|{e}|isDefEq"
  let ci ← getConstInfo ``Tools.ShippingSrm15Graph.ran_designCorr_of_graphOf
  let ei ← getConstInfo ``Tests.Compiler.Srm15ExpStmt.Exp_mutation_noHkids
  if (← isDefEq ci.type (ei.value?.getD (mkConst ei.name))) then throwError "SRM15 AUDIT FAILED: the mutated expected statement (hkids deleted) was ACCEPTED"
  logInfo m!"S15EXPMUT|hkids-deleted expected form rejected"
  for (a, b) in [(``Tests.Compiler.Srm15GraphTest.topshareM_corr15, ``Tests.Compiler.Srm12CorrTest.topshareM_corr), (``Tests.Compiler.Srm15GraphTest.topshareQ_corr15, ``Tests.Compiler.Srm12CorrTest.topshareQ_corr)] do
    let ca ← getConstInfo a
    let cb ← getConstInfo b
    unless (← isDefEq ca.type cb.type) do throwError "SRM15 AUDIT FAILED: {a} and {b} differ"
    logInfo m!"S15VS12|{a}|{b}|isDefEq"
  for n in [``Tools.ShippingSrm15Graph.graphOf, ``Tools.ShippingSrm15Graph.FirstOcc, ``Tools.ShippingSrm15Graph.GraphCovers, ``Tools.ShippingSrm15Graph.DefsProv] do
    let ci ← getConstInfo n
    logInfo m!"S15DEF|{n}|{((← ppExpr (ci.value?.getD default)).pretty 100000).replace "\n" " "}"

end
