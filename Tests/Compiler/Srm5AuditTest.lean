import Tests.Compiler.Srm5ParentQTest
import Tests.Compiler.Srm5HeightTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm5AuditExpected
import Tools.ShippingKidsChildIfaceM
-- BUILT (unit SRM5): s5k4 exit 0 (dev run, default heartbeats, no heartbeat option); the final-SHA rebuild is in REPORT-SRM5.md.
-- SCOPE (SRM5, audits).  For each audited SRM5 theorem: (1) PREMISE TABLE: every binder (index, binderInfo, name, Prop-or-data, type) is printed as an `S5PREM` / `S5DATA` line and the WHOLE table (every binder of every audited theorem,
-- in order) must EQUAL the committed `Tests/Compiler/Srm5AuditExpected.lean` (`expectedRows`) EXACTLY (list equality of the normalised tuples; a changed type, an added/removed/reordered binder, a changed implicit/data binder FAILS the build)
-- AND the committed text view `scripts/srm5/PREMISES.txt`, line for line.  NEGATIVE FIXTURES: three mutations of the actual table (a changed Prop binder type with the same name; an added data binder; a reordered binder list) are REJECTED by the comparator.
-- REGENERATION (from the head revision): `./.cluster/qbuild.sh build Tests.Compiler.Srm5AuditTest > LOG 2>&1; python3 scripts/srm5/gen_audit.py LOG` rewrites `Tests/Compiler/Srm5AuditExpected.lean` and `scripts/srm5/PREMISES.txt` from the `S5PREM`/`S5DATA` lines
-- (a stale expected file makes the first build fail AFTER printing the rows, so the log is always available).  Binder names containing `_hyg` (anonymous arrows) are normalised to `_anon`.
-- (2) BINDER AUDIT: no hypothesis restates the conclusion (`isDefEq` at reducible transparency; control: a hand-made wrapper IS caught), and no hypothesis of the height theorems mentions the uniform children's check (`kidsPass`/`kidCheck`).
-- (3) CLOSURE AUDIT: standard axioms only, no old `RefLaws`/`RealChild`/`InvW`/`MachineRan`/`MachineClosesAt`/`ChildBnd`/`KidFacts`-form constant in the closure, every height theorem uses `hcheck`, the parent instances use the identification lemma and
-- `memCallee_kidHeight` and do NOT route through `kidsNC_designCheck_of_kidsPass` / `core_kidsPass_deep_ranA` (the uniform route; `kids_designCheck_inA` is reported as an `S5NOTE`: it can enter through `KidFactsA.toNC` of the plain callee, whose `check`
-- field is projected away).  CONTROLS: every forbidden root exists; the old-form `kidsChild_of_realM` IS caught by the same walk.  Examples do not make the class complete; `RealChildA` is a history of past synthesis results.
-- NOT guaranteed: that the hypotheses are TRUE or satisfiable in general (only that they are the listed ones); the type strings are `ppExpr` renderings in the head environment.  No `sorry`, no `axiom`, no `native_decide`.
set_option Elab.async false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm5AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited5 SRM5 theorems -/
def audited5 : List Name :=
  [``Tools.ShippingSrm5Height.hcheck_memKids, ``Tools.ShippingSrm5Height.hcheck_memModule, ``Tools.ShippingSrm5Height.hcheck_ord,
   ``Tools.ShippingSrm5Height.hcheck_edge, ``Tools.ShippingSrm5Height.hcheck_unresolved, ``Tools.ShippingSrm5Height.hcheck_norank,
   ``Tools.ShippingSrm5Height.hcheck_notBelow, ``Tools.ShippingSrm5Height.hcheck_selfInst, ``Tools.ShippingSrm5Height.hcheck_misnamed,
   ``Tools.ShippingSrm5Height.hcheck_eq_designCheck,
   ``Tools.ShippingSrm5Ident.inst_target_ranA, ``Tools.ShippingSrm5Ident.inst_target_ord_ranA,
   ``Tools.ShippingSrm5Transfer.kids_textCheck_inA, ``Tools.ShippingSrm5Transfer.kidsH_body_ranA, ``Tools.ShippingSrm5Transfer.kids_hcheck_inA,
   ``Tools.ShippingSrm5Transfer.kidsH_pass_ranA, ``Tools.ShippingSrm5Transfer.textCheckI_shipped, ``Tools.ShippingSrm5Transfer.kidsNC_hcheck,
   ``Tools.ShippingSrm5TransferM.kids_textCheck_inAM, ``Tools.ShippingSrm5TransferM.kidsH_body_ranAM, ``Tools.ShippingSrm5TransferM.kids_hcheck_inAM,
   ``Tools.ShippingSrm5Deep.deepChild_kidHeightAM, ``Tools.ShippingSrm5Deep.memCallee_kidHeight,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_kidHeight, ``Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_kidHeight,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM3_kidHeight, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.leafP_kidHeight, ``Tests.Compiler.SharedLeafMemKidIfaceTest.wrapP_kidHeight,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_kidHeight, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck,
   ``Tests.Compiler.Srm5HeightTest.unbalanced_height_ok, ``Tests.Compiler.Srm5HeightTest.uniform_fails,
   ``Tests.Compiler.Srm5HeightTest.mut_self, ``Tests.Compiler.Srm5HeightTest.mut_backEdge, ``Tests.Compiler.Srm5HeightTest.mut_unresolved,
   ``Tests.Compiler.Srm5HeightTest.mut_norank, ``Tests.Compiler.Srm5HeightTest.mut_misnamed, ``Tests.Compiler.Srm5HeightTest.balanced_reproduces]

/-- the HEIGHT theorems whose hypotheses must not mention the uniform children's check -/
def heightThms : List Name :=
  [``Tools.ShippingSrm5Transfer.kidsH_body_ranA, ``Tools.ShippingSrm5Transfer.kids_hcheck_inA, ``Tools.ShippingSrm5Transfer.kidsH_pass_ranA,
   ``Tools.ShippingSrm5Transfer.kidsNC_hcheck, ``Tools.ShippingSrm5TransferM.kidsH_body_ranAM, ``Tools.ShippingSrm5TransferM.kids_hcheck_inAM,
   ``Tools.ShippingSrm5Deep.deepChild_kidHeightAM, ``Tools.ShippingSrm5Deep.memCallee_kidHeight,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck]

/-- the PARENT instances that must not route through the uniform children's check -/
def parentInstances : List Name :=
  [``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck]


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

/-- the text line of a row (the format of `scripts/srm5/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S5{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

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
      if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingDesignSV.kidsPass || c == ``Tools.ShippingChecksDesign.kidCheck) then return true
    return false

end Tests.Compiler.Srm5AuditTest

open Tests.Compiler.Srm5AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm5AuditTest.wrapper_mutation) do throwError "SRM5 AUDIT FAILED: the wrapper control was not caught"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited5 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S5THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S5THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM5 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  -- the whole table equals the committed expected table, EXACTLY
  match tableDiff actual Tests.Compiler.Srm5AuditExpected.expectedRows with
  | some msg => throwError "SRM5 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm5AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm5/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM5 AUDIT FAILED: scripts/srm5/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM5 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm5AuditExpected.expectedRows with
    | none => throwError "SRM5 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S5FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S5TABLE|{audited5.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm5/PREMISES.txt"
  for thm in heightThms do
    if (← mentionsUniform thm) then throwError "SRM5 AUDIT FAILED: a hypothesis of {thm} mentions the uniform children's check"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM5 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM5 AUDIT FAILED: control walk found no old-form constant"
  let uniform : List Name := [``Tools.ShippingSrm4Parent.kidsNC_designCheck_of_kidsPass, ``Tools.ShippingKidsSelfA.core_kidsPass_deep_ranA]
  let uniformInfo : Name := ``Tools.ShippingSeqChildDeepKidCheckA.kids_designCheck_inA
  for u in uniform do
    unless (← getEnv).contains u do throwError "SRM5 AUDIT FAILED: the uniform-route constant {u} does not exist (vacuous audit)"
  for thm in audited5 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM5 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM5 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    let s := thm.toString
    let has (x : String) : Bool := (s.splitOn x).length > 1
    if has "kidHeight" || has "hcheck" || has "kids_hcheck" || has "kidsNC_hcheck" || has "kidsH_" then
      unless cl.contains ``Tools.ShippingSrm5Height.hcheck do throwError "SRM5 AUDIT FAILED: hcheck not in the closure of {thm}"
    if parentInstances.contains thm then
      for u in uniform do
        if cl.contains u then throwError "SRM5 AUDIT FAILED: {thm} routes through the uniform children's check {u}"
      unless cl.contains ``Tools.ShippingSrm5Ident.inst_target_ord_ranA do throwError "SRM5 AUDIT FAILED: the identification lemma is not in the closure of {thm}"
      unless cl.contains ``Tools.ShippingSrm5Deep.memCallee_kidHeight do throwError "SRM5 AUDIT FAILED: memCallee_kidHeight is not in the closure of {thm}"
    if parentInstances.contains thm then
      -- INFORMATION: `kids_designCheck_inA` may be in the closure through the plain callee's `KidFactsA.toNC` (its `check` field is projected away, not used)
      logInfo m!"S5NOTE|{thm}|kids_designCheck_inA in closure: {cl.contains uniformInfo}"
    stdAxioms thm
    logInfo m!"S5CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary; uniform route {if parentInstances.contains thm then "absent" else "not asserted"}"

end
