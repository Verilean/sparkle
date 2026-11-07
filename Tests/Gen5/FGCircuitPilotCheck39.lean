import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tests.Gen5.FGCircuitPilotCheck33
set_option autoImplicit false
-- FG circuit pilot S2s check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §44.

/-! # FGCircuitPilotCheck39 (light)

ONE comparison function (`Check33.cmp`: the same constants are normalised and `isDefEq` runs at DEFAULT transparency) is used for the positive case and for every mutant.

1. SIGNATURE: the complete type of the ported main theorem `core_tripleA_mainX` (context predicate `O.adm` carried by the bundle, telescope family `RefLawsATeleX O.quiet O.adm`) against an independently written statement, with mutants (the old `AdmCtx O.quiet` context, the old telescope bundle, no exception fact, no telescope premise, the precondition dropped).
2. STEPS (surface types only, NOT the closure of the proofs): the ported theorems mention `RefLawsAOpsX` and not the old `AdmCtx` / `RefLawsAOps`; the original theorem still mentions `AdmCtx` (control, so the test discriminates); the specialisation `RefLawsAOps.toX` mentions `AdmCtx`.
3. AXIOMS (every name is looked up with `contains` BEFORE `collectAxioms`).
This covers the ported development up to `core_tripleA_main` (S2s steps 1-17); the S2dKids / S2hHist3 / S2mReach3 / S2nAdm consumers and `hftCoreCloses_of_kidsR''` are NOT ported (docs §44). -/
namespace Tests.Gen5.FGCircuitPilotCheck39
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 tyOf binderNames)
open Tests.Gen5.FGCircuitPilotCheck33 (cmp agree differ binderKinds)

/-! ## independently written statements -/

/-- the real one: `hA : O.adm`, `T : RefLawsATeleX O.quiet O.adm`, post `OutQ ∧ OkExc` -/
def ExpMain : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    O.adm mctx cctx → RefLawsATeleX O.quiet O.adm mref cref → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (OutQ O.quiet)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e)
/-- the plain `AdmCtx O.quiet` context instead of the predicate of the bundle -/
def MainPlainAdm : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    AdmCtx O.quiet mctx cctx → RefLawsATeleX O.quiet O.adm mref cref → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (OutQ O.quiet)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e)
/-- the old telescope bundle (quantified over `AdmCtx quiet`) -/
def MainOldTele : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    O.adm mctx cctx → RefLawsATele O.quiet mref cref → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (OutQ O.quiet)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e)
/-- the telescope family dropped -/
def MainNoTele : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    O.adm mctx cctx → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (OutQ O.quiet)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e)
/-- no exception fact -/
def MainNoExc : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    O.adm mctx cctx → RefLawsATeleX O.quiet O.adm mref cref → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (OutQ O.quiet)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun _ w => OutQ O.quiet w)
/-- the precondition is trivial (any world) -/
def MainTrivPre : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    O.adm mctx cctx → RefLawsATeleX O.quiet O.adm mref cref → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (fun _ => True)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e)
/-- the post-condition `OutQ` replaced by `True` -/
def MainTrivPost : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOpsX MkRefd mref cref),
    O.adm mctx cctx → RefLawsATeleX O.quiet O.adm mref cref → ∀ (declName : Name),
    Tools.ShippingChildInv.Triple mctx mref cctx cref (OutQ O.quiet)
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      (fun _ => True) (fun e w => OutQ O.quiet w ∧ OkExc e)

/-! ## 1. SIGNATURE -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck39
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  let t ← tyOf `Tools.ShippingChildMainA.core_tripleA_mainX
  agree "core_tripleA_mainX" t (q "ExpMain")
  let names := binderNames (← instantiateMVars t) |>.map (·.toString)
  let exp := ["mctx", "mref", "cctx", "cref", "O", "hA", "T", "declName"]
  unless names == exp do throwError "core_tripleA_mainX binders: {names}"
  let mut n : Nat := 0
  for mu in ["MainPlainAdm", "MainOldTele", "MainNoTele", "MainNoExc", "MainTrivPre", "MainTrivPost"] do
    differ s!"core_tripleA_mainX vs {mu}" t (q mu); n := n + 1
  logInfo m!"FGCIRCUIT39 SIGNATURE: the complete type of core_tripleA_mainX (binders {exp}; the context is the predicate O.adm carried by the bundle, the telescope family is RefLawsATeleX O.quiet O.adm) matches the independently written statement under the same comparison function and transparency as every mutant; {n} mutants rejected (plain AdmCtx context, old telescope bundle, no telescope premise, no exception fact, trivial precondition, trivial postcondition)"

/-! ## 2. STEPS (surface types only) -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let ported : List Name := [
    `Tools.ShippingChildMainA.core_tripleA_mainX, `Tools.ShippingChildMainA.childKeepsA_mainX,
    `Tools.ShippingChildMainA.bodyStepA_mainX, `Tools.ShippingChildComposeA.bodyKeepsA_of_teleX,
    `Tools.ShippingChildLegacyTailA.legacyTailA_genericX, `Tools.ShippingChildLegacyTailA.legacyTailA_of_stepX,
    `Tools.ShippingChildTeleMainA.core_tripleA_main_tlX]
  let mut c : Nat := 0
  for nm in ported do
    unless env.contains nm do throwError "STEPS: {nm} does not exist"
    let u := (← tyOf nm).getUsedConstants
    if u.contains ``AdmCtx then throwError "{nm} mentions AdmCtx"
    if u.contains ``RefLawsAOps then throwError "{nm} mentions the old RefLawsAOps"
    if u.contains ``RefLawsATele then throwError "{nm} mentions the old RefLawsATele"
    unless u.contains ``RefLawsAOpsX do throwError "{nm} does not take RefLawsAOpsX"
    c := c + 4
  -- controls: the originals still mention the old forms; the specialisation mentions AdmCtx
  let orig := (← tyOf `Tools.ShippingChildMainA.core_tripleA_main).getUsedConstants
  unless orig.contains ``AdmCtx && orig.contains ``RefLawsAOps do throwError "control: the original core_tripleA_main lost AdmCtx / RefLawsAOps"
  let spec := (← tyOf `Tools.ShippingChildInvA.RefLawsAOps.toX).getUsedConstants
  unless spec.contains ``RefLawsAOps && spec.contains ``RefLawsAOpsX do throwError "control: RefLawsAOps.toX"
  let sdef ← getConstInfo `Tools.ShippingChildInvA.RefLawsAOps.toX
  let su := (sdef.value?.map (·.getUsedConstants)).getD #[]
  unless su.contains ``AdmCtx do throwError "control: RefLawsAOps.toX does not set adm := AdmCtx quiet"
  c := c + 3
  logInfo m!"FGCIRCUIT39 STEPS: {ported.length} ported theorems mention RefLawsAOpsX and neither AdmCtx nor the old RefLawsAOps / RefLawsATele; the originals keep their old forms (control) and RefLawsAOps.toX is the specialisation adm := AdmCtx quiet; {c} structural checks (surface types only: the constants occurring in the statement's type, NOT the closure of the proofs)"

/-! ## 3. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  for l in [
    "NOT PORTED (S2s3 pod): S2dKids (machineChild_ifaceK), S2jKid, S1zClose/S1qLinked/Linked/RunLocal/S2aClose and the Laws / Start structures (Tools/ShippingGen2Defs.lean) onto the context-predicate bundle; S2hHist2's port is an early stale copy (needs regeneration); S2hHist3 hftCoreCloses_of_kidsH, S2mReach3 hftCoreCloses_of_kidsR, S2nAdm hftCoreCloses_of_kidsR'",
    "hftCoreCloses_of_kidsR'' (without hdown) is therefore NOT stated or proved"] do
    logInfo m!"FGCIRCUIT39 REMAINING {l}"

run_cmd liftTermElabM do
  let names : List Name := [
    `Tools.ShippingChildMainA.core_tripleA_mainX, `Tools.ShippingChildMainA.childKeepsA_mainX,
    `Tools.ShippingChildComposeA.bodyKeepsA_of_teleX, `Tools.ShippingChildLegacyTailA.legacyTailA_genericX,
    `Tools.ShippingChildLegacyTailA.legacyTailA_of_stepX, `Tools.ShippingChildTeleMainA.core_tripleA_main_tlX,
    `Tools.ShippingChildInvA.RefLawsAOps.toX]
  let env ← getEnv
  for nm in names do
    unless env.contains nm do throwError "AXIOMS: {nm} does not exist"
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT39 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck39
