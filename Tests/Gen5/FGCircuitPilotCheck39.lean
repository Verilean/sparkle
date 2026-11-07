import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmS2nAdm
import Tests.Gen5.FGCircuitPilotCheck33
set_option autoImplicit false
-- FG circuit pilot S2s check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §44.

/-! # FGCircuitPilotCheck39 (light)

ONE comparison function (`Check33.cmp`: the same constants are normalised and `isDefEq` runs at DEFAULT transparency) is used for the positive case and for every mutant.

1. SIGNATURE: the complete type of the ported main theorem `core_tripleA_mainX` (context predicate `O.adm` carried by the bundle, telescope family `RefLawsATeleX O.quiet O.adm`) against an independently written statement, with mutants (the old `AdmCtx O.quiet` context, the old telescope bundle, no exception fact, no telescope premise, the precondition dropped).
2. STEPS (surface types only, NOT the closure of the proofs): the ported theorems mention `RefLawsAOpsX` and not the old `AdmCtx` / `RefLawsAOps`; the original theorem still mentions `AdmCtx` (control, so the test discriminates); the specialisation `RefLawsAOps.toX` mentions `AdmCtx`.
3. AXIOMS (every name is looked up with `contains` BEFORE `collectAxioms`).
4. (S2s5) GOAL: the complete type of `hftCoreCloses_of_kidsR''` (no `hdown`, no `hadm`; premises `hD hG hT hs h0` named) against an independently written statement, 5 mutants rejected, structural checks, axioms.
This covers the ported development up to `core_tripleA_main` (S2s steps 1-17) and the S2s4/S2s5 path (CallsGatePinned, S1zClose, S2dKids, S2hHist3, S2mReach/2/3, S2nAdm); the named premises of the goal stay unsupplied (docs §44). -/
namespace Tests.Gen5.FGCircuitPilotCheck39
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 tyOf binderNames)
open Tests.Gen5.FGCircuitPilotCheck33 (cmp agree differ binderKinds)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitCover (RootReader)
open Tools.ShippingFGCircuitS2dKids (HftKidsGates)
open Tools.ShippingFGCircuitS1kStmt (hftHttp hftTlp)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

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
      (fun _ _ => True) (fun e w => OutQ O.quiet w ∧ OkExc e)

/-! ## goal statements (S2s5) -/

/-- the real one -/
def ExpGoal : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    StartX L mctx cctx w → CellPrem MkRefd mref cref → ∀ {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData →
    HftKidsGates (envAt cref w) →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w →
    ProfStepRX L.O w → ProfOffW mref cref w → HftCoreCloses mctx mref cctx cref w
/-- the start condition dropped -/
def GoalNoStart : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    CellPrem MkRefd mref cref → ∀ {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData →
    HftKidsGates (envAt cref w) →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w →
    ProfStepRX L.O w → ProfOffW mref cref w → HftCoreCloses mctx mref cctx cref w
/-- the telescope row premise dropped -/
def GoalNoTele : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    StartX L mctx cctx w → CellPrem MkRefd mref cref → ∀ {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData →
    HftKidsGates (envAt cref w) →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w →
    ProfStepRX L.O w → ProfOffW mref cref w → HftCoreCloses mctx mref cctx cref w
/-- the profile premise `h0` dropped -/
def GoalNoProf : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    StartX L mctx cctx w → CellPrem MkRefd mref cref → ∀ {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData →
    HftKidsGates (envAt cref w) →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w →
    ProfStepRX L.O w → HftCoreCloses mctx mref cctx cref w
/-- the conclusion trivialised -/
def GoalTrivConcl : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    StartX L mctx cctx w → CellPrem MkRefd mref cref → ∀ {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData →
    HftKidsGates (envAt cref w) →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w →
    ProfStepRX L.O w → ProfOffW mref cref w → True
/-- the kids' gates premise dropped -/
def GoalNoGates : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    StartX L mctx cctx w → CellPrem MkRefd mref cref → ∀ {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w →
    ProfStepRX L.O w → ProfOffW mref cref w → HftCoreCloses mctx mref cctx cref w

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
    "NOT PORTED: ImplCorA, LinkA, LoopsCP (nothing on the path imports them); the premises hD hG hT hs h0 of hftCoreCloses_of_kidsR'' (DRowEnvRX, DiagEnvRX, TeleRX, ProfStepRX, ProfOffW) and the telescope family RefLawsATeleX are NAMED and unsupplied",
    "ported, not rebuilt as part of the S2s3 closure: the S2s5 path files are listed in docs §44"] do
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

/-! ## 4. GOAL (S2s5) -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck39
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  let g := `Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR''
  unless (← getEnv).contains g do throwError "GOAL: {g} does not exist"
  let t ← tyOf g
  agree "hftCoreCloses_of_kidsR''" t (q "ExpGoal")
  let mut n : Nat := 0
  for mu in ["GoalNoStart", "GoalNoTele", "GoalNoProf", "GoalTrivConcl", "GoalNoGates"] do
    differ s!"hftCoreCloses_of_kidsR'' vs {mu}" t (q mu); n := n + 1
  let u := t.getUsedConstants
  unless u.contains ``LawsX do throwError "GOAL: not stated for LawsX"
  if u.contains ``AdmDownR then throwError "GOAL mentions AdmDownR"
  if u.contains ``Tools.ShippingFGCircuitS2mReach.AdmDownR then throwError "GOAL mentions AdmDownR"
  if u.contains ``AdmCtx then throwError "GOAL mentions AdmCtx"
  -- control: the original S2m statement still has hdown
  let old := (← tyOf `Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsR).getUsedConstants
  unless old.contains `Tools.ShippingFGCircuitS2mReach.AdmDownR do throwError "control: the original hftCoreCloses_of_kidsR lost AdmDownR"
  logInfo m!"FGCIRCUIT39 GOAL: the complete type of hftCoreCloses_of_kidsR'' matches the independently written statement (LawsX bundle; no hdown, no hadm; named premises hD hG hT hs h0 and CellPrem / reader / gates); {n} mutants rejected (no start condition, no telescope premise, no profile premise, trivial conclusion, no kids gates); its type mentions LawsX and neither AdmDownR nor AdmCtx while the S2m original still mentions AdmDownR (control); surface types only, NOT the proof closure"

run_cmd liftTermElabM do
  let names : List Name := [
    `Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR'', `Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_root,
    `Tools.ShippingFGCircuitS2sAdmS2nAdm.admRootX_toX, `Tools.ShippingFGCircuitS2sAdmS2nAdm.startX_of_root,
    `Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsRX, `Tools.ShippingFGCircuitS2mReach.jqhr_coreX,
    `Tools.ShippingFGCircuitS2mReach.ropsRX, `Tools.ShippingFGCircuitS2mReach.jqhr_headX,
    `Tools.ShippingFGCircuitS2dKids.machineChild_ifaceKX, `Tools.ShippingFGCircuitS2dKids.hftCoreCloses_of_kidsKX,
    `Tools.ShippingFGCircuitS2hHist.hftCoreCloses_of_kidsHX, `Tools.ShippingFGCircuitS1zClose.synth_hftPcieOutByte_finalOffLNLX,
    `Tools.ShippingCallsGatePinned.machineClosesAtA_of_gateKids'X]
  let env ← getEnv
  let mut missing : List Name := []
  for nm in names do
    unless env.contains nm do missing := nm :: missing
  unless missing.isEmpty do throwError "AXIOMS2: names that do not exist: {missing}"
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT39 AXIOMS2: {names.length} names of the S2s5 path (looked up before collectAxioms), standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck39
