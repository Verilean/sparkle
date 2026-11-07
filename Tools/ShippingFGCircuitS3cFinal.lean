import Tools.ShippingFGCircuitS3aFinal
import Tools.ShippingFGCircuitS3cTop
set_option autoImplicit false
-- FG circuit pilot S3c: final statement v7 = v6 WITHOUT hadm and hdown. The closing step is the context-predicate route (hftTop_of_runRX, hftCoreCloses_of_kidsR'', synth_hftPcieOutByte_finalOffLNLX). hT is stated at TeleRX (the X form of the telescope law); this is a changed premise, see docs/FG-CIRCUIT-PILOT.md S52. No sorry/axiom/native_decide/TRUSTED/law.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3cFinal
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid Tools.ShippingFGCircuitS2jTop
open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe
open Meta Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildInv (Res)
open Tools.ShippingFGCircuitFinal4 (EntryGates)

open Tools.ShippingFGCircuitS1xNoRaw Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2rFinal (synth_hftPcieOutByte_finalOffCombined2 HftFinalStmtOffCombined2)

open Tools.ShippingFGCircuitS2vLink (HftFinalStmtOffCombined3 synth_hftPcieOutByte_finalOffCombined3)
open Tools.ShippingFGCircuitS2tHft (hftObCDT_T)
open Tools.ShippingFGCircuitS1wTbl (RecFact)
open Tools.ShippingFGCircuitS2iTbl

open Tools.ShippingFGCircuitS2yFinal (cdvT HftFinalStmtOffCombined4 synth_hftPcieOutByte_finalOffCombined4)
open Tools.ShippingFGCircuitS1qLinked (core_envOkOff)
open Tools.ShippingFGCircuitS1qEndpoint (postEntryOff)
open Tools.ShippingFGCircuitS1qHead (headAtOff_of_cellPrem)
open Tools.ShippingEnvSnapshot (envFrame_getConstInfo)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)

open Tools.ShippingFGCircuitS2zFinal (HftFinalStmtOffCombined5 synth_hftPcieOutByte_finalOffCombined5 startEnvOk_of_run)

open Tools.ShippingFGCircuitS3aFinal (startKidsOk_of_run)
open Tools.ShippingFGCircuitS3cTop
open Tools.ShippingFGCircuitS2sAdmS2nAdm
open Tools.ShippingFGCircuitS2zFinal (startEnvOk_of_run)
open Tools.ShippingFGCircuitS1zClose (synth_hftPcieOutByte_finalOffLNLX)
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingChildInvA Tools.ShippingChildCacheA


section Bridge
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem leafStep_ofX {O : RefLawsAOps MkRefd mref cref} {w w' : Void IO.RealWorld}
    (h : LeafStepX O.quiet (AdmCtx O.quiet) mref cref w w') : LeafStep O.quiet mref cref w w' := by
  cases h with
  | frame mctx cctx p w a hp => exact .frame mctx cctx p w a hp
  | diag mctx cctx p w a hp => exact .diag mctx cctx p w a hp
  | throws mctx cctx p w a hp => exact .throws mctx cctx p w a hp
  | cacheSet mctx cctx v w u w' a hr => exact .cacheSet mctx cctx v w u w' a hr
  | depthSet mctx cctx v w u w' a hr => exact .depthSet mctx cctx v w u w' a hr

theorem leafStep_toX {O : RefLawsAOps MkRefd mref cref} {w w' : Void IO.RealWorld}
    (h : LeafStep O.quiet mref cref w w') : LeafStepX O.quiet (AdmCtx O.quiet) mref cref w w' := by
  cases h with
  | frame mctx cctx p w a hp => exact .frame mctx cctx p w a hp
  | diag mctx cctx p w a hp => exact .diag mctx cctx p w a hp
  | throws mctx cctx p w a hp => exact .throws mctx cctx p w a hp
  | cacheSet mctx cctx v w u w' a hr => exact .cacheSet mctx cctx v w u w' a hr
  | depthSet mctx cctx v w u w' a hr => exact .depthSet mctx cctx v w u w' a hr

theorem reached_ofX {O : RefLawsAOps MkRefd mref cref} {w₀ w : Void IO.RealWorld}
    (h : ReachedX O.quiet (AdmCtx O.quiet) mref cref w₀ w) : Reached O.quiet mref cref w₀ w := by
  induction h with
  | start => exact .start
  | step _ hs ih => exact .step ih (leafStep_ofX hs)

/-- the v6 forms of `hD hG hs` give the X forms at `L.toX` (the reachability predicates agree) -/
theorem drowEnvRX_of_R (L : Laws mref cref) {e : Environment} {w₀ : Void IO.RealWorld} (h : DRowEnvR L.O e w₀) : DRowEnvRX L.toX.O e w₀ :=
  fun mctx cctx α p a hp w hq hR hr => h mctx cctx p a hp w hq hR (reached_ofX hr)

theorem diagEnvRX_of_R (L : Laws mref cref) {e : Environment} {w₀ : Void IO.RealWorld} (h : DiagEnvR L.O e w₀) : DiagEnvRX L.toX.O e w₀ :=
  fun mctx cctx α p a hp w hq hR hr => h mctx cctx p a hp w hq hR (reached_ofX hr)

theorem profStepRX_of_R (L : Laws mref cref) {w₀ : Void IO.RealWorld} (h : ProfStepR L.O w₀) : ProfStepRX L.toX.O w₀ :=
  fun w w' hr hl h0 => h w w' (reached_ofX hr) (leafStep_ofX hl) h0

end Bridge

/-- **v7**: v6 with `hadm` and `hdown` REMOVED (14 binders). `hD hG hs` keep their v6 propositions; `hT` is the telescope law in its context-predicate form `TeleRX` (contexts `AdmCtx quiet`, not `AdmCtx (quietR ..)`): this is the one premise whose proposition differs from v6's `TeleR` (docs S52) -/
def HftFinalStmtOffCombined7 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined7 : HftFinalStmtOffCombined7 := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hD hG hT hs h0
  have hkg := Tools.ShippingFGCircuitS3aKids.startKidsOk_sound (startKidsOk_of_run hcell hr)
  obtain ⟨hΔ, hΓ, hrec⟩ := Tools.ShippingFGCircuitS2zPin.startEnvOk_sound (startEnvOk_of_run hcell hr)
  have hD' := drowEnvRX_of_R L hD
  have hG' := diagEnvRX_of_R L hG
  have hs' := profStepRX_of_R L hs
  have hstartX : StartX L.toX mctx cctx w := ⟨hstart.1, jqc_toX hstart.2⟩
  exact synth_hftPcieOutByte_finalOffLNLX cdvT Tools.ShippingFGCircuitS2oOb.HftObCDT (fun _ h => h)
    Tools.ShippingFGCircuitS2kLink.hftRootLink L.toX lvl env₀ hstartX hr hcell hchk hRdH hRdT
    (hftObCDT_T _ hΔ hΓ hrec)
    (hftTop_of_runRX L lvl env₀ hstart hcell hchk hRdH hRdT hkg hD' hG' hT hs' h0)
    (hftCoreCloses_of_kidsR'' L.toX hstartX hcell hRdH hRdT (hftKidsGates_of_facts hkg) hD' hG' hT hs' h0)

end Tools.ShippingFGCircuitS3cFinal

#print axioms Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7
