import Tools.ShippingFGCircuitS3dFinal
import Tests.Gen5.FGCircuitPilotCheck46
import Tests.Gen5.FGCircuitPilotCheck46r
set_option autoImplicit false
-- FG circuit pilot Check47 (S3d): the complete type of v8 (pilot entry, lvl₀, hadm/hdown/lvl/hreadH/hreadT removed, hT at TeleRX) against an independently written statement (Exp8; the only reuse is Check46.ExpTX = the TeleRX form via quietRX / Laws.toX, unavoidable since TeleRX is stated through them), mutants (each premise dropped; entry = True checker / ordinary Off run / another root; start world / context not the run's; TeleR instead of TeleRX; hadm/hdown/lvl/readers back; other level in hchk or GPt; weakened / other conclusion; other carrier), a binder-list comparison with v6, v7 and v7r, and standard axioms only.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck47
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS1kStmt (hftRoot hftHttp hftTlp)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuit Tools.ShippingFGCircuitCover
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.IR.AST
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen2 Tools.ShippingFGCircuitS1kPkg Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitBridge Tools.ShippingFGCircuitRoots Tools.ShippingGen5FG Tools.ShippingGen5DeclConnect Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead Tools.ShippingFGCircuitS1tFinal
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod NmRoot NmHttp NmTlp RootData HttpData TlpData Pre)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck33 (ExpQuiet ExpD ExpG ExpT ExpPS ExpDown ExpProfOff)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)
open Tests.Gen5.FGCircuitPilotCheck43 (CVT)
open Tests.Gen5.FGCircuitPilotCheck44 (NmHttpX)
open Tests.Gen5.FGCircuitPilotCheck46 (ExpTX binderNames)
open Tests.Gen5.FGCircuitPilotCheck46r (lvlZero lvlSucc chkTrue)

/-- **v8, written again.** Knobs: the premises (Bool); `ent` = the run's entry (0 = `synthesizeCombinationalOffR pilotReaderOk root`, 1 = the same with the True check, 2 = the ordinary Off entry); `st` = the start premise (0 = `Start L mctx cctx w`, 1 = some other context, 2 = some other world); `tele` (0 = TeleRX, 1 = TeleR); the old premises `hadm`/`hdown`, a `lvl` binder with the two readers back; the levels of `hchk` / `GPt`; the reach environment, root, post-run root; conclusion parts; carrier. -/
noncomputable def Exp8 (nStart nRun nCell nChk nD nG nT nPS nProf : Bool) (ent st tele : Nat) (addAdm addDown readers : Bool)
    (lvC lvG : Lean.Expr → Nat) (c1 c2 : Bool) (eA : EnvK) (root postRoot : Name) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Pre nStart (if st == 0 then Start L mctx cctx w else if st == 1 then (∃ mctx2 : Cx, Start L mctx2 cctx w) else (∃ w2 : W, Start L mctx cctx w2)) (
    Pre nRun (RunsTo (if ent == 0 then synthesizeCombinationalOffR Tools.ShippingFGCircuitS3b2Final.pilotReaderOk root
                      else if ent == 1 then synthesizeCombinationalOffR (fun _ _ => true) root
                      else synthesizeCombinationalOff root) mctx mref cctx cref w (b, D') w') (
    Pre nCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    Pre nChk (CheckedStart lvC env₀ cref w root hftRootType hftRootValue RootData) (
    Pre readers (RootReader lvC (envAt cref w) NmHttp HttpData) (
    Pre readers (RootReader lvC (envAt cref w) NmTlp TlpData) (
    Pre addAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (eA cref w w' env₀) w) mctx cctx) (
    Pre addDown (ExpDown L.O (eA cref w w' env₀) w) (
    Pre nD (ExpD L.O (eA cref w w' env₀) w) (
    Pre nG (ExpG L.O (eA cref w w' env₀) w) (
    Pre nT (if tele == 0 then ExpTX L (eA cref w w' env₀) w else ExpT L.O (eA cref w w' env₀) w) (
    Pre nPS (ExpPS L.O w) (
    Pre nProf (ExpProfOff mref cref w) (
    (if c1 then (∃ raw, PostRunOff mctx mref cctx cref w postRoot D' b raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvG (envAt cref w)) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot shHft mm b D' p) else True))))))))))))))

noncomputable def F8 (nStart nRun nCell nChk nD nG nT nPS nProf : Bool := true) (ent st tele : Nat := 0) (addAdm addDown readers : Bool := false)
    (lvC lvG : Lean.Expr → Nat := Tools.ShippingFGCircuitS3b2Reader.lvl₀) (c1 c2 : Bool := true)
    (eA : EnvK := eS) (root postRoot : Name := NmRoot) (CV : CDRel := CVT) : Prop :=
  Exp8 nStart nRun nCell nChk nD nG nT nPS nProf ent st tele addAdm addDown readers lvC lvG c1 c2 eA root postRoot CV

noncomputable def F8_real : Prop := F8
noncomputable def F8Mu_noStart : Prop := F8 (nStart := false)
noncomputable def F8Mu_noRun : Prop := F8 (nRun := false)
noncomputable def F8Mu_noCell : Prop := F8 (nCell := false)
noncomputable def F8Mu_noChk : Prop := F8 (nChk := false)
noncomputable def F8Mu_noD : Prop := F8 (nD := false)
noncomputable def F8Mu_noG : Prop := F8 (nG := false)
noncomputable def F8Mu_noT : Prop := F8 (nT := false)
noncomputable def F8Mu_noPS : Prop := F8 (nPS := false)
noncomputable def F8Mu_noProf : Prop := F8 (nProf := false)
-- the entry: another reader (True checker), the ordinary Off run, another root
noncomputable def F8Mu_entTrue : Prop := F8 (ent := 1)
noncomputable def F8Mu_entOff : Prop := F8 (ent := 2)
noncomputable def F8Mu_root : Prop := F8 (root := NmHttpX)
noncomputable def F8Mu_postRoot : Prop := F8 (postRoot := NmHttpX)
-- the start world / context are the run's
noncomputable def F8Mu_startCtx : Prop := F8 (st := 1)
noncomputable def F8Mu_startWorld : Prop := F8 (st := 2)
-- the law boundary: old TeleR in place of TeleRX; reach environment
noncomputable def F8Mu_teleV6 : Prop := F8 (tele := 1)
noncomputable def F8Mu_reachEnd : Prop := F8 (eA := eE)
noncomputable def F8Mu_reachEnv0 : Prop := F8 (eA := e0)
-- the removed premises back
noncomputable def F8Mu_addAdm : Prop := F8 (addAdm := true)
noncomputable def F8Mu_addDown : Prop := F8 (addDown := true)
noncomputable def F8Mu_addBoth : Prop := F8 (addAdm := true) (addDown := true)
noncomputable def F8Mu_readersBack : Prop := F8 (readers := true)
-- the level: other level in hchk / in GPt (and the readers)
noncomputable def F8Mu_lvlChk0 : Prop := F8 (lvC := lvlZero)
noncomputable def F8Mu_lvlChkSucc : Prop := F8 (lvC := lvlSucc)
noncomputable def F8Mu_lvlGPt0 : Prop := F8 (lvG := lvlZero)
noncomputable def F8Mu_lvlGPtSucc : Prop := F8 (lvG := lvlSucc)
-- the conclusion: weakened / other carrier
noncomputable def F8Mu_noC1 : Prop := F8 (c1 := false)
noncomputable def F8Mu_noC2 : Prop := F8 (c2 := false)
noncomputable def F8Mu_carrierZ : Prop := F8 (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)

def unfold47 : List Name := [``Tools.ShippingFGCircuitS3dFinal.HftFinalStmtOffCombined8, ``Tools.ShippingFGCircuitS3cFinal.HftFinalStmtOffCombined7,
  ``Tools.ShippingFGCircuitS3b2Final.HftFinalStmtOffCombined7R, ``Tools.ShippingFGCircuitS3aFinal.HftFinalStmtOffCombined6,
  ``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT, ``Tools.ShippingFGCircuitS2mReach.TeleRX]
def norm47 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold47.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck47 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  let f8ty ← tyOf ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8
  let f8 ← norm47 f8ty
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined8" f8 (← norm37 (Q "F8_real"))
  for mu in ["F8Mu_noStart", "F8Mu_noRun", "F8Mu_noCell", "F8Mu_noChk", "F8Mu_noD", "F8Mu_noG", "F8Mu_noT", "F8Mu_noPS", "F8Mu_noProf",
      "F8Mu_entTrue", "F8Mu_entOff", "F8Mu_root", "F8Mu_postRoot", "F8Mu_startCtx", "F8Mu_startWorld", "F8Mu_teleV6", "F8Mu_reachEnd", "F8Mu_reachEnv0",
      "F8Mu_addAdm", "F8Mu_addDown", "F8Mu_addBoth", "F8Mu_readersBack", "F8Mu_lvlChk0", "F8Mu_lvlChkSucc", "F8Mu_lvlGPt0", "F8Mu_lvlGPtSucc",
      "F8Mu_noC1", "F8Mu_noC2", "F8Mu_carrierZ"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined8 vs {mu}" f8 (← norm37 (Q mu)); nm := nm + 1
  -- v8 is none of v6, v7, v7r
  let f6ty ← tyOf ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6
  let f7ty ← tyOf ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7
  let f7rty ← tyOf ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined8 vs the v6 theorem's type" f8 (← norm47 f6ty); nm := nm + 1
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined8 vs the v7 theorem's type" f8 (← norm47 f7ty); nm := nm + 1
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined8 vs the v7r theorem's type" f8 (← norm47 f7rty); nm := nm + 1
  -- binder lists
  let bl (t : Lean.Expr) : MetaM (List Name) := do return binderNames ((← unfoldDefinition? t).getD t)
  let b6 ← bl f6ty
  let b7 ← bl f7ty
  let b7r ← bl f7rty
  let b8 ← bl f8ty
  unless b8 == b7r.filter (fun n => n != `hadm && n != `hdown) do throwError "v8 is not v7r minus [hadm, hdown]: v7r {b7r}, v8 {b8}"
  unless b8 == b7.filter (fun n => n != `lvl && n != `hreadH && n != `hreadT) do throwError "v8 is not v7 minus [lvl, hreadH, hreadT]: v7 {b7}, v8 {b8}"
  unless b7r == b6.filter (fun n => n != `lvl && n != `hreadH && n != `hreadT) do throwError "v7r is not v6 minus [lvl, hreadH, hreadT]: v6 {b6}, v7r {b7r}"
  unless b6.length == 25 && b7.length == 23 && b7r.length == 22 && b8.length == 20 do
    throwError "binder counts: v6 {b6.length}, v7 {b7.length}, v7r {b7r.length}, v8 {b8.length}"
  for n in [`lvl, `hreadH, `hreadT, `hadm, `hdown] do
    unless !b8.contains n do throwError "v8 still has {n}"
  logInfo m!"FGCIRCUIT47 BINDERS (9 implicit + explicit): v6 ({b6.length} = 9 + 16) {b6}; v7 ({b7.length} = 9 + 14) {b7}; v7r ({b7r.length} = 9 + 13) {b7r}; v8 ({b8.length} = 9 + 11) {b8}; v8 = v7r minus [hadm, hdown] = v7 minus [lvl, hreadH, hreadT]; hT is stated at TeleRX (as v7), every other premise keeps its v6 proposition (docs S54)"
  logInfo m!"FGCIRCUIT47 SIGNATURES: the complete type of synth_hftPcieOutByte_finalOffCombined8 equals the independently written Exp8 under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths; the only reuse is Check46.ExpTX for TeleRX); {nm} mutants rejected (each premise dropped; True checker / ordinary Off run / other root / other post-run root; start context / world not the run's; TeleR for TeleRX; hadm / hdown / both / the two readers back; other level in hchk and in GPt; reach environment end / initial; weakened conclusion parts; other carrier; v6, v7, v7r)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8, ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7,
    ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R, ``Tools.ShippingFGCircuitS3b2Final.pilotReaderOk_sound, ``Tools.ShippingFGCircuitS3b2Final.readerOk_of_run,
    ``Tools.ShippingFGCircuitS3b2Core.offR_to_off]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT47 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck47
