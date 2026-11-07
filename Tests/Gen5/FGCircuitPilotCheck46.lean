import Tools.ShippingFGCircuitS3cFinal
import Tests.Gen5.FGCircuitPilotCheck45
set_option autoImplicit false
-- FG circuit pilot Check46 (S3c): the complete type of v7 (hadm and hdown removed, hT at the context-predicate form) against an independently written statement, mutants (each premise dropped, hadm/hdown back, hT in the v6 form, env/root/carrier/conclusion changes, v6 itself), a binder-list comparison with v6, and standard axioms only. Same criterion FGCircuitCmp.stmtEq for the expected statement and every mutant.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck46
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist (KidEv)
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS1tFinal (CDRel)
open Tools.ShippingFGCircuitS1kStmt (hftRoot hftHttp hftTlp)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuit Tools.ShippingFGCircuitCover
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.IR.AST
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod NmRoot NmHttp NmTlp RootData HttpData TlpData Pre EntryOf)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck33 (ExpQuiet ExpD ExpG ExpT ExpPS ExpDown ExpProfOff)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)
open Tests.Gen5.FGCircuitPilotCheck43 (CVT)
open Tests.Gen5.FGCircuitPilotCheck44 (NmHttpX)

/-- the telescope law in the context-predicate form, written again: strengthened quiet predicate with the reachability of the X bundle, context predicate `AdmCtx quiet` -/
def ExpTX (L : Laws mref cref) (e : Environment) (w₀ : W) : Prop :=
  RefLawsATeleX (quietRX (Tools.ShippingGen2.Laws.toX L).O.quiet (Tools.ShippingGen2.Laws.toX L).O.adm mref cref e w₀) (Tools.ShippingGen2.Laws.toX L).O.adm mref cref

/-- **v7, written again.** Knobs: each premise (Bool), `tele` (0 = hT at TeleRX as in v7, 1 = hT in the v6 form TeleR), the old premises hadm/hdown back, the reach environment, root, post-run root, carrier, conclusion parts, the diagnostic entry. -/
noncomputable def Exp7 (nStart nRun nCell nChk nRH nRT nD nG nT nPS nProf : Bool) (tele : Nat) (addAdm addDown : Bool)
    (c1 c2 diag : Bool) (eA : EnvK) (root postRoot : Name) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Pre nStart (Start L mctx cctx w) (
    Pre nRun (RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w') (
    Pre nCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    Pre nChk (CheckedStart lvl env₀ cref w root hftRootType hftRootValue RootData) (
    Pre nRH (RootReader lvl (envAt cref w) NmHttp HttpData) (
    Pre nRT (RootReader lvl (envAt cref w) NmTlp TlpData) (
    Pre addAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (eA cref w w' env₀) w) mctx cctx) (
    Pre addDown (ExpDown L.O (eA cref w w' env₀) w) (
    Pre nD (ExpD L.O (eA cref w w' env₀) w) (
    Pre nG (ExpG L.O (eA cref w w' env₀) w) (
    Pre nT (if tele == 0 then ExpTX L (eA cref w w' env₀) w else ExpT L.O (eA cref w w' env₀) w) (
    Pre nPS (ExpPS L.O w) (
    Pre nProf (ExpProfOff mref cref w) (
    (if c1 then (∃ raw, PostRunOff mctx mref cctx cref w postRoot D' b raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot shHft mm b D' p) else True))))))))))))))

noncomputable def F7 (nStart nRun nCell nChk nRH nRT nD nG nT nPS nProf : Bool := true) (tele : Nat := 0) (addAdm addDown : Bool := false)
    (c1 c2 : Bool := true) (diag : Bool := false) (eA : EnvK := eS) (root postRoot : Name := NmRoot) (CV : CDRel := CVT) : Prop :=
  Exp7 nStart nRun nCell nChk nRH nRT nD nG nT nPS nProf tele addAdm addDown c1 c2 diag eA root postRoot CV

noncomputable def F7_real : Prop := F7
noncomputable def F7Mu_noStart : Prop := F7 (nStart := false)
noncomputable def F7Mu_noRun : Prop := F7 (nRun := false)
noncomputable def F7Mu_noCell : Prop := F7 (nCell := false)
noncomputable def F7Mu_noChk : Prop := F7 (nChk := false)
noncomputable def F7Mu_noRH : Prop := F7 (nRH := false)
noncomputable def F7Mu_noRT : Prop := F7 (nRT := false)
noncomputable def F7Mu_noD : Prop := F7 (nD := false)
noncomputable def F7Mu_noG : Prop := F7 (nG := false)
noncomputable def F7Mu_noT : Prop := F7 (nT := false)
noncomputable def F7Mu_noPS : Prop := F7 (nPS := false)
noncomputable def F7Mu_noProf : Prop := F7 (nProf := false)
noncomputable def F7Mu_teleV6 : Prop := F7 (tele := 1)
noncomputable def F7Mu_addAdm : Prop := F7 (addAdm := true)
noncomputable def F7Mu_addDown : Prop := F7 (addDown := true)
noncomputable def F7Mu_addBoth : Prop := F7 (addAdm := true) (addDown := true)
noncomputable def F7Mu_reachEnd : Prop := F7 (eA := eE)
noncomputable def F7Mu_reachEnv0 : Prop := F7 (eA := e0)
noncomputable def F7Mu_root : Prop := F7 (root := NmHttpX)
noncomputable def F7Mu_postRoot : Prop := F7 (postRoot := NmHttpX)
noncomputable def F7Mu_noC1 : Prop := F7 (c1 := false)
noncomputable def F7Mu_noC2 : Prop := F7 (c2 := false)
noncomputable def F7Mu_diag : Prop := F7 (diag := true)
noncomputable def F7Mu_carrierZ : Prop := F7 (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)

/-- what the X bundle at `L.toX` is: its context predicate is `AdmCtx L.O.quiet` and its quiet predicate is `L.O.quiet` (by `rfl`) -/
theorem toX_adm {mref : Rf1} {cref : Rf2} (L : Laws mref cref) : (Tools.ShippingGen2.Laws.toX L).O.adm = AdmCtx L.O.quiet := rfl
theorem toX_quiet {mref : Rf1} {cref : Rf2} (L : Laws mref cref) : (Tools.ShippingGen2.Laws.toX L).O.quiet = L.O.quiet := rfl

def unfold46 : List Name := [``Tools.ShippingFGCircuitS3cFinal.HftFinalStmtOffCombined7, ``Tools.ShippingFGCircuitS3aFinal.HftFinalStmtOffCombined6,
  ``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT, ``TeleRX]
def norm46 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold46.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e

/-- the names of the leading binders of a type (implicit and explicit) -/
partial def binderNames (e : Lean.Expr) : List Name :=
  match e with
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck46 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  let f7ty ← tyOf ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7
  let f7 ← norm46 f7ty
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined7" f7 (← norm37 (Q "F7_real"))
  for mu in ["F7Mu_noStart", "F7Mu_noRun", "F7Mu_noCell", "F7Mu_noChk", "F7Mu_noRH", "F7Mu_noRT", "F7Mu_noD", "F7Mu_noG", "F7Mu_noT", "F7Mu_noPS", "F7Mu_noProf",
      "F7Mu_teleV6", "F7Mu_addAdm", "F7Mu_addDown", "F7Mu_addBoth", "F7Mu_reachEnd", "F7Mu_reachEnv0", "F7Mu_root", "F7Mu_postRoot", "F7Mu_noC1", "F7Mu_noC2", "F7Mu_diag", "F7Mu_carrierZ"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined7 vs {mu}" f7 (← norm37 (Q mu)); nm := nm + 1
  -- v6 and v5 are not v7
  let f6ty ← tyOf ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined7 vs the v6 theorem's type" f7 (← norm46 f6ty); nm := nm + 1
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined7 vs the v5 theorem's type" f7 (← norm46 (← tyOf ``Tools.ShippingFGCircuitS2zFinal.synth_hftPcieOutByte_finalOffCombined5)); nm := nm + 1
  -- binder lists (names of the leading binders of the stated types, in order)
  let b6 := binderNames f6ty
  let b7 := binderNames f7ty
  let expected7 := b6.filter fun n => n != `hadm && n != `hdown
  unless b7 == expected7 do throwError "binder list of v7 is not v6 without hadm/hdown: v6 {b6}, v7 {b7}"
  unless b6.length == 16 && b7.length == 14 do throwError "binder counts: v6 {b6.length}, v7 {b7.length}"
  unless !b7.contains `hadm && !b7.contains `hdown do throwError "v7 still has hadm/hdown"
  logInfo m!"FGCIRCUIT46 BINDERS: v6 ({b6.length}) {b6}; v7 ({b7.length}) {b7}; v7 = v6 minus [hadm, hdown]; hT keeps its name but is stated at TeleRX (docs S52)"
  logInfo m!"FGCIRCUIT46 SIGNATURES: the complete type of synth_hftPcieOutByte_finalOffCombined7 equals the independently written Exp7 under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths); {nm} mutants rejected (each premise dropped, hadm/hdown/both back, hT in the v6 form TeleR, reach environment end/initial, other root, other post-run root, conclusion parts dropped, diagnostic entry, carrier Z, the v6 and v5 theorem types)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7, ``Tools.ShippingFGCircuitS3cTop.hftTop_of_runRX,
    ``Tools.ShippingFGCircuitS3cTop.kid_shipsResWX, ``Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR'',
    ``Tools.ShippingFGCircuitS2kRun.machineRunJQH_of_closesHOffX, ``Tools.ShippingFGCircuitS2kRun.soundX_served_EX, ``Tools.ShippingFGCircuitS2jKid.kidRunKX]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT46 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck46
