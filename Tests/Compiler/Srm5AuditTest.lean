import Tests.Compiler.Srm5ParentQTest
import Tests.Compiler.Srm5HeightTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingKidsChildIfaceM
-- BUILT (unit SRM5): s5j1 exit 0 (dev run, default heartbeats, no heartbeat option); the final-SHA rebuild is in REPORT-SRM5.md.
-- SCOPE (SRM5, audits).  For each audited5 SRM5 theorem: (1) PREMISE TABLE: every binder (kind, name, Prop-or-data, type) is printed as an `S5PREM` / `S5DATA` line (machine-generated, extracted into `scripts/srm5/PREMISES.txt`), and the list of
-- HYPOTHESIS (Prop) binder names must equal the EXPECTED list; (2) BINDER AUDIT: no hypothesis restates the conclusion (`isDefEq` at reducible transparency), and no hypothesis of the height theorems mentions the uniform children's check (`kidsPass`/`kidCheck`);
-- (3) CLOSURE AUDIT: standard axioms only, no old `RefLaws`/`RealChild`/`InvW`/`MachineRan`/`MachineClosesAt`/`ChildBnd`/`KidFacts`-form constant in the closure, the transfer/instance theorems use `hcheck` and the identification lemma, and
-- the parent instances do NOT route through `kidsNC_designCheck_of_kidsPass` / `core_kidsPass_deep_ranA` (the uniform route; `kids_designCheck_inA` is reported as an `S5NOTE`: it can enter through `KidFactsA.toNC` of the plain callee, whose `check` field is projected away).  CONTROLS: every forbidden root exists; the old-form `kidsChild_of_realM` IS caught by the same walk;
-- the binder audit REJECTS a hand-made mutation (a theorem whose hypothesis is its own conclusion).  Examples do not make the class complete; `RealChildA` is a history of past synthesis results.
-- No `sorry`, no `axiom`, no `native_decide`.
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

-- BEGIN EXPECTED
def expectedPrem : List (Name × List String) :=
  [(`Tools.ShippingSrm5Height.hcheck_memKids, ["hr", "ht", "hk"]),
   (`Tools.ShippingSrm5Height.hcheck_memModule, ["hr"]),
   (`Tools.ShippingSrm5Height.hcheck_ord, ["hr", "ht", "hk"]),
   (`Tools.ShippingSrm5Height.hcheck_edge, ["hr", "hc", "hm"]),
   (`Tools.ShippingSrm5Height.hcheck_unresolved, ["hr", "hm", "hu"]),
   (`Tools.ShippingSrm5Height.hcheck_norank, ["hr", "hm", "hu"]),
   (`Tools.ShippingSrm5Height.hcheck_notBelow, ["hr", "hm", "hrm", "hge"]),
   (`Tools.ShippingSrm5Height.hcheck_selfInst, ["hr", "hm"]),
   (`Tools.ShippingSrm5Height.hcheck_misnamed, ["hr", "hm", "hc", "hne"]),
   (`Tools.ShippingSrm5Height.hcheck_eq_designCheck, ["a._@._internal._hyg.0"]),
   (`Tools.ShippingSrm5Ident.inst_target_ranA, ["ok", "hbody", "hC", "hslots", "hdomB", "ran", "a._@._internal._hyg.0"]),
   (`Tools.ShippingSrm5Ident.inst_target_ord_ranA, ["ok", "hbody", "hC", "hslots", "hdomB", "hnomem", "ran", "a._@._internal._hyg.0"]),
   (`Tools.ShippingSrm5Transfer.kids_textCheck_inA, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "hsl", "hfne", "outTy", "hnomem", "hkidP", "hkidW", "hkidT", "hargs", "hkidIn", "hkidClk", "hpost", "ran", "hon", "hoty", "hms"]),
   (`Tools.ShippingSrm5Transfer.kidsH_body_ranA, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "outTy", "hnomem", "hpost", "ran", "hrank", "hkidH", "hmsD"]),
   (`Tools.ShippingSrm5Transfer.kids_hcheck_inA, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "hsl", "hfne", "outTy", "hnomem", "hkidP", "hkidW", "hkidT", "hargs", "hkidIn", "hkidClk", "hpost", "ran", "hon", "hoty", "hms", "hrb", "hrank", "hkidH"]),
   (`Tools.ShippingSrm5Transfer.kidsH_pass_ranA, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "outTy", "hnomem", "hpost", "ran", "hrank", "hkidH"]),
   (`Tools.ShippingSrm5Transfer.textCheckI_shipped, ["h", "ht", "hports"]),
   (`Tools.ShippingSrm5Transfer.kidsNC_hcheck, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "hsl", "hfne", "outTy", "hnomem", "hkid", "hcw", "hargs", "hpost", "ran", "hon", "hoty", "hrb", "hrank", "hkidH"]),
   (`Tools.ShippingSrm5TransferM.kids_textCheck_inAM, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "hsl", "hfne", "outTy", "hkidP", "hkidW", "hkidT", "hargs", "hkidIn", "hkidClk", "hpost", "ran", "hon", "hoty", "hms"]),
   (`Tools.ShippingSrm5TransferM.kidsH_body_ranAM, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "hfne", "outTy", "hpost", "ran", "hrkmem", "hrank", "hkidH", "hmsD"]),
   (`Tools.ShippingSrm5TransferM.kids_hcheck_inAM, ["ok", "hbody", "hC", "hslots", "hdomB", "hins", "hsl", "hfne", "outTy", "hkidP", "hkidW", "hkidT", "hargs", "hkidIn", "hkidClk", "hpost", "ran", "hon", "hoty", "hms", "hrb", "hrkmem", "hrank", "hkidH"]),
   (`Tools.ShippingSrm5Deep.deepChild_kidHeightAM, ["T", "ok", "hbody", "hC", "hslots", "hdomB", "hins", "hsl", "hfne", "outTy", "hlo", "hcw", "hargs", "hon", "hoty", "hsep", "entry", "closes", "hrb", "hrkmem", "hrank", "hkidH"]),
   (`Tools.ShippingSrm5Deep.memCallee_kidHeight, ["T", "hC", "hord", "hmemT", "hKid", "hcw", "hargs", "hon", "hoty", "entry", "hrb", "hrkmem", "hrk", "hKidH"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_kidHeight, ["T", "entryL", "hrb", "hrkmem"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_kidHeight, ["T", "entryL", "entry", "hrb", "hl", "hrkmem", "hleaf"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM3_kidHeight, ["T", "entryL", "entry", "hrb", "hl", "hrkmem", "hleaf"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck, ["T", "hA", "entryL", "entry₁", "entry₂", "entry", "hcore", "hpost", "hw", "hrkmem", "hrT", "hrW", "hrW3", "hrL"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.leafP_kidHeight, ["hR0", "hcl", "hr"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.wrapP_kidHeight, ["T", "hR0", "hcl", "entry", "hrb", "hl", "hrkmem", "hleaf"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_kidHeight, ["T", "hR0", "hcl", "entry", "hrb", "hl", "hrkmem", "hleaf"]),
   (`Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck, ["T", "hA", "hR0", "hcl", "entry₁", "entry₂", "entry", "hcore", "hpost", "hw", "hrkmem", "hrT", "hrP", "hrQ", "hrL"]),
   (`Tests.Compiler.Srm5HeightTest.unbalanced_height_ok, ["hRt", "hAt"]),
   (`Tests.Compiler.Srm5HeightTest.uniform_fails, []),
   (`Tests.Compiler.Srm5HeightTest.mut_self, []),
   (`Tests.Compiler.Srm5HeightTest.mut_backEdge, []),
   (`Tests.Compiler.Srm5HeightTest.mut_unresolved, []),
   (`Tests.Compiler.Srm5HeightTest.mut_norank, []),
   (`Tests.Compiler.Srm5HeightTest.mut_misnamed, []),
   (`Tests.Compiler.Srm5HeightTest.balanced_reproduces, [])]
-- END EXPECTED

/-- rows `(index, kind, name, isProp, type)` of the binders of a theorem's type -/
def premiseRows (thm : Name) : MetaM (List (Nat × String × String × Bool × String)) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut rows : List (Nat × String × String × Bool × String) := []
    let mut i := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let isP ← Meta.isProp d.type
      let bi := match d.binderInfo with
        | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst" | .default => "explicit"
      rows := rows ++ [(i, bi, d.userName.toString, isP, ((← ppExpr d.type).pretty 100000).replace "\n" " ")]
      i := i + 1
    return rows

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
  -- (1)+(2) premise table and binder audit
  for thm in audited5 do
    let rows ← premiseRows thm
    let hyps := rows.filter (·.2.2.2.1) |>.map (·.2.2.1)
    for (i, bi, nm, isP, ty) in rows do
      logInfo m!"S5{if isP then "PREM" else "DATA"}|{thm}|{i}|{bi}|{nm}|{ty}"
    logInfo m!"S5HYPS|{thm}|{String.intercalate "," hyps}"
    if (← restatesConclusion thm) then throwError "SRM5 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
    match expectedPrem.lookup thm with
    | some exp =>
      unless exp == hyps do throwError "SRM5 AUDIT FAILED: the hypotheses of {thm} are {hyps}, expected {exp}"
    | none => pure ()
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
