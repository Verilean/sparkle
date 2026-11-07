import Tools.ShippingFGCircuitS2yFinal
import Tests.Gen5.FGCircuitPilotCheck37
import Tests.Gen5.FGCircuitCmp
set_option autoImplicit false
-- FG circuit pilot S2y check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §48.

/-! # FGCircuitPilotCheck43 (light; ONE criterion `FGCircuitCmp.stmtEq` for the expected statement and every mutant, as in Check37/42)

1. FINAL4: the COMPLETE type of `synth_hftPcieOutByte_finalOffCombined4` (v3 with `hcd` replaced by `EnvDefs`/`EnvCtors`/`RecFact` at `envAt cref w`, carrier `CDT env []`) against an independently written `ExpFinal4` (Check37's `ExpFinal2` with the `HftRootLink` binder removed and the `hcd` premise replaced by the three conditions). Mutants: each condition's environment moved to the end world / env₀ / a world independent of the run, another root, another output shape, another carrier (Z/Y/X/old instead of T), each of the three conditions dropped, other tables (`none`), `hcd` kept in addition (at the same env and at the end world), a different premise dropped, ...
2. AXIOMS: standard only. WHENEVER the final wrapper changes, this check must be updated in the same commit. -/
namespace Tests.Gen5.FGCircuitPilotCheck43
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist (MissE JQH EQH CacheE KidEv)
open Tools.ShippingFGCircuitS2rFinal
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2jTop (HftCallDec)
open Tools.ShippingFGCircuitS2gGates (HftKidsGateFacts)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt
open Tools.ShippingFGCircuitS1tFinal (cdvZ cdvY cdvOld CDRel)
open Tools.ShippingFGCircuitS1rCD (HftObCDZ)
open Tools.ShippingFGCircuitS1uSrc (HftRootLink)
open Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitS1iEnv Tools.ShippingGen2 Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuit
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead
open Tools.ShippingFGCircuitS1kPkg Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1tFinal
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod ZS ZE idF idW NmRoot NmHttp NmTlp ShE RootData HttpData TlpData Pre EntryOf iteStep binderInfos)
open Tests.Gen5.FGCircuitPilotCheck28 (kmissR)
open Tests.Gen5.FGCircuitPilotCheck30 (ExpDec)
open Tests.Gen5.FGCircuitPilotCheck27 (ExpHK MuSwap MuSwapName MuHttpTwice MuTlpTwice MuHttpOnly MuTlpOnly MuWholeBoth MuTrue)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck33 (ExpQuiet ExpD ExpG ExpT ExpPS ExpDown ExpProfOff ProfOnW DNoReach DNoReads DStart GNoReach TPlain TNoReach DownUp DownId PSNoReach PSStart PSAnyStep)

open Tools.ShippingFGCircuitS2yFinal (HftFinalStmtOffCombined4 synth_hftPcieOutByte_finalOffCombined4 cdvT)
open Tools.ShippingFGCircuitS1mCD (EnvDefs EnvCtors DefRow CtorRow)
open Tools.ShippingFGCircuitS1wTbl (RecFact)
open Tools.ShippingFGCircuitS1tFinal (cdvX)
open Tools.ShippingFGCircuitS1pCD (HftObCDX)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)

/-- the carrier of `hftObCDT_T`, written out: `CDT` in the empty closure environment -/
def CVT : CDRel := fun env e α v => Tools.ShippingFGCircuitS2iDT.CDT env [] e α v

/-- **`HftFinalStmtOffCombined4`, written again** (no `HftRootLink`; `hcd` replaced by the three conditions, each with its own environment knob; `keepHcd` re-adds `hcd`). -/
noncomputable def ExpFinal4 (CV : CDRel) (DT : Name → Option DefRow) (GT : Name → Option CtorRow)
    (diag oldArt nDefs nCtors nRec keepHcd needAdm needKgf c1 c2 : Bool)
    (dE cE' rE hE' eA cE : EnvK) (root postRoot : Name) (sh : SigShape) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Start L mctx cctx w →
    RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w' →
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref →
    CheckedStart lvl env₀ cref w root hftRootType hftRootValue RootData →
    RootReader lvl (envAt cref w) NmHttp HttpData →
    RootReader lvl (envAt cref w) NmTlp TlpData →
    Pre nDefs (EnvDefs (dE cref w w' env₀) DT) (
    Pre nCtors (EnvCtors (cE' cref w w' env₀) GT) (
    Pre nRec (RecFact (rE cref w w' env₀)) (
    Pre keepHcd (CV (hE' cref w w' env₀) hftRootValue (MonoTy shHft) synth_hftPcieOutByte) (
    Pre needAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (eA cref w w' env₀) w) mctx cctx) (
    Pre true (ExpDown L.O (eA cref w w' env₀) w) (
    Pre true (ExpD L.O (eA cref w w' env₀) w) (
    Pre true (ExpG L.O (eA cref w w' env₀) w) (
    Pre true (ExpT L.O (eA cref w w' env₀) w) (
    Pre true (ExpPS L.O w) (
    Pre true (ExpProfOff mref cref w) (
    Pre needKgf (ExpHK (eA cref w w' env₀)) (
    (if c1 then (∃ raw, PostRunOff mctx mref cctx cref w postRoot D' b raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      (if oldArt then RootArtifactMono (cE cref w w' env₀) (GPt (ι := ι) lvl (cE cref w w' env₀)) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot sh mm b D' p
       else RootArtifactMonoV CV (cE cref w w' env₀) (GPt (ι := ι) lvl (cE cref w w' env₀)) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot sh mm b D' p)) else True)))))))))))))

noncomputable def Dl := Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Delta
noncomputable def Gm := Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Gamma

noncomputable def FD4 (CV : CDRel := CVT) (DT : Name → Option DefRow := Dl) (GT : Name → Option CtorRow := Gm)
    (diag oldArt : Bool := false) (nDefs nCtors nRec : Bool := true) (keepHcd : Bool := false) (needAdm needKgf c1 c2 : Bool := true)
    (dE cE' rE hE' eA cE : EnvK := eS) (root postRoot : Name := NmRoot) (sh : SigShape := ShE) : Prop :=
  ExpFinal4 CV DT GT diag oldArt nDefs nCtors nRec keepHcd needAdm needKgf c1 c2 dE cE' rE hE' eA cE root postRoot sh

/-! ## mutants: every one differs from the real FD4 in exactly one knob -/

noncomputable def FD4_real : Prop := FD4
noncomputable def Mu_dEnd : Prop := FD4 (dE := eE)
noncomputable def Mu_dEnv0 : Prop := FD4 (dE := e0)
noncomputable def Mu_cEnd : Prop := FD4 (cE' := eE)
noncomputable def Mu_cEnv0 : Prop := FD4 (cE' := e0)
noncomputable def Mu_rEnd : Prop := FD4 (rE := eE)
noncomputable def Mu_rEnv0 : Prop := FD4 (rE := e0)
noncomputable def Mu_allEnd : Prop := FD4 (dE := eE) (cE' := eE) (rE := eE)
noncomputable def Mu_allEnv0 : Prop := FD4 (dE := e0) (cE' := e0) (rE := e0)
noncomputable def Mu_dIndep : Prop := ∀ {a : W}, FD4 (dE := fun cref _ _ _ => envAt cref a)
noncomputable def Mu_cIndep : Prop := ∀ {a : W}, FD4 (cE' := fun cref _ _ _ => envAt cref a)
noncomputable def Mu_rIndep : Prop := ∀ {a : W}, FD4 (rE := fun cref _ _ _ => envAt cref a)
noncomputable def Mu_concEnd : Prop := FD4 (cE := eE)
noncomputable def Mu_concEnv0 : Prop := FD4 (cE := e0)
noncomputable def Mu_reachEnd : Prop := FD4 (eA := eE)
noncomputable def Mu_root : Prop := FD4 (root := NmHttp)
noncomputable def Mu_postRoot : Prop := FD4 (postRoot := NmHttp)
noncomputable def Mu_output : Prop := FD4 (sh := { ShE with res := .one (.bits 16) })
noncomputable def Mu_noDefs : Prop := FD4 (nDefs := false)
noncomputable def Mu_noCtors : Prop := FD4 (nCtors := false)
noncomputable def Mu_noRec : Prop := FD4 (nRec := false)
noncomputable def Mu_noAll : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false)
noncomputable def Mu_tabDefs : Prop := FD4 (DT := fun _ => none)
noncomputable def Mu_tabCtors : Prop := FD4 (GT := fun _ => none)
noncomputable def Mu_hcdKept : Prop := FD4 (keepHcd := true)
noncomputable def Mu_hcdKeptEnd : Prop := FD4 (keepHcd := true) (hE' := eE)
noncomputable def Mu_hcdOnly : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (keepHcd := true)
noncomputable def Mu_carrierZ : Prop := FD4 (CV := cdvZ)
noncomputable def Mu_carrierY : Prop := FD4 (CV := cdvY)
noncomputable def Mu_carrierX : Prop := FD4 (CV := cdvX)
noncomputable def Mu_carrierOld : Prop := FD4 (CV := cdvOld)
noncomputable def Mu_carrierOldArt : Prop := FD4 (oldArt := true)
noncomputable def Mu_diag : Prop := FD4 (diag := true)
noncomputable def Mu_noAdm : Prop := FD4 (needAdm := false)
noncomputable def Mu_noKgf : Prop := FD4 (needKgf := false)
noncomputable def Mu_noC1 : Prop := FD4 (c1 := false)
noncomputable def Mu_noC2 : Prop := FD4 (c2 := false)
/-- hlink-style regression: the `HftRootLink` binder is back -/
noncomputable def Mu_hlink : Prop := HftRootLink → FD4

def unfold43 : List Name := [``HftFinalStmtOffCombined4, ``cdvT]

/-- Check37's normalisation, after the new statement's own definition (and its carrier) is unfolded -/
def norm43 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold43.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck43 ++ Name.mkSimple n)
  let fin ← norm43 (← tyOf ``synth_hftPcieOutByte_finalOffCombined4)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined4" fin (← norm37 (Q "FD4_real"))
  let mut nm : Nat := 0
  for mu in ["Mu_dEnd", "Mu_dEnv0", "Mu_cEnd", "Mu_cEnv0", "Mu_rEnd", "Mu_rEnv0", "Mu_allEnd", "Mu_allEnv0", "Mu_dIndep", "Mu_cIndep", "Mu_rIndep", "Mu_concEnd", "Mu_concEnv0", "Mu_reachEnd",
      "Mu_root", "Mu_postRoot", "Mu_output", "Mu_noDefs", "Mu_noCtors", "Mu_noRec", "Mu_noAll", "Mu_tabDefs", "Mu_tabCtors", "Mu_hcdKept", "Mu_hcdKeptEnd", "Mu_hcdOnly",
      "Mu_carrierZ", "Mu_carrierY", "Mu_carrierX", "Mu_carrierOld", "Mu_carrierOldArt", "Mu_diag", "Mu_noAdm", "Mu_noKgf", "Mu_noC1", "Mu_noC2", "Mu_hlink"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined4 vs {mu}" fin (← norm37 (Q mu)); nm := nm + 1
  -- the v3 statements (with hcd; Z/Y/X) are not the new one
  for (old, what) in [(`Tools.ShippingFGCircuitS2vLink.synth_hftPcieOutByte_finalOffCombined3_Z, "v3 Z"), (`Tools.ShippingFGCircuitS2vLink.synth_hftPcieOutByte_finalOffCombined3_Y, "v3 Y"),
      (`Tools.ShippingFGCircuitS2vLink.synth_hftPcieOutByte_finalOffCombined3_X, "v3 X"), (`Tools.ShippingFGCircuitS2rFinal.synth_hftPcieOutByte_finalOffCombined2_Z, "v2 Z")] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined4 vs the {what} statement" fin (← norm37 (← tyOf old)); nm := nm + 1
  logInfo m!"FGCIRCUIT43 SIGNATURES-FINAL4: the complete type of synth_hftPcieOutByte_finalOffCombined4 (v3 with hcd replaced by EnvDefs/EnvCtors/RecFact at envAt cref w, carrier CDT env [] = cdvT) equals the independently written ExpFinal4 under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths); {nm} mutants rejected (each condition's environment at the end world / env₀ / a world independent of the run, the reach and conclusion environments, another root / post root / output shape, each condition dropped and all three, other tables, hcd kept in addition (same env, end world, only hcd), carrier Z/Y/X/old/old artifact, diag entry, a premise dropped, hlink back, and the v3/v2 statements)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``synth_hftPcieOutByte_finalOffCombined4, `Tools.ShippingFGCircuitS2tHft.hftObCDT_T]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT43 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck43
