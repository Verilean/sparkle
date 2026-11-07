import Tools.ShippingFGCircuitS3jStart
set_option autoImplicit false
-- FG circuit pilot S3j, unit 2: the final statement v10 = v9 with `hstart` narrowed to the residual of `Start` that is NOT supplied, each conjunct its own named hypothesis (`hquiet`, `hsynth`, `hcache`), and the run `hr` of the checked wrapper `pilotEntry3` (so `AdmCtx` and `dv w = 0` of `Start` come from the run's own checks).  v9 is untouched.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §60.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3jFinal
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
open Tools.ShippingFGCircuitS3b2Reader (lvl₀ rootReaderB rootReaderB_sound)
open Tools.ShippingFGCircuitS1hGates (entryGatesB entryGatesB_sound)
open Tools.ShippingFGCircuitS3f2Exp (rootMD rootMD_eq)
open Tools.ShippingFGCircuitS3b2Final (pilotReaderOk pilotReaderOk_sound readerOk_of_run)
open Tools.ShippingFGCircuitS3b2Core (offR_to_off)
open Tools.ShippingFGCircuitS3cFinal (synth_hftPcieOutByte_finalOffCombined7)

open Tools.ShippingFGCircuitS3jStart (pilotEntry3 admCtx_of_pilotEntry3 dv_of_pilotEntry3 entry2_of_pilotEntry3)
open Tools.ShippingFGCircuitS3f2Final (HftFinalStmtOffCombined9 synth_hftPcieOutByte_finalOffCombined9 pilotReaderOk2)
open Tools.ShippingChildBndCore (sv)
open Tools.ShippingChildCacheA (CacheInvA)

/-- **`Start` from the residual and the run's checks**: `AdmCtx` from the wrapper's `canUnfold?` check, `dv w = 0` from its depth check; `quiet w`, `sv w = some synthesizeChild` and the cache half are the residual hypotheses -/
theorem start_of_residual {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hr : RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w')
    (hquiet : L.O.quiet w) (hsynth : sv w = some synthesizeChild) (hcache : CacheInvA L.O (cv w)) :
    Start L mctx cctx w :=
  ⟨admCtx_of_pilotEntry3 hr L.O.quiet, ⟨⟨hquiet, hsynth, dv_of_pilotEntry3 hr⟩, hcache⟩⟩

/-- **v10** (11 binders): v9 with `hstart` replaced by the three conjuncts of `Start` that nothing supplies — `hquiet : L.O.quiet w`, `hsynth : sv w = some synthesizeChild`, `hcache : CacheInvA L.O (cv w)` — and `hr` a run of the checked wrapper `pilotEntry3` (the S3f2 entry behind the `canUnfold?` and depth-0 checks).  Gone from `Start`: `AdmCtx L.O.quiet mctx cctx` and `dv w = 0`.  Binders: `L hquiet hsynth hcache hr hcell hD hG hT hs h0`. -/
def HftFinalStmtOffCombined10 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hquiet : L.O.quiet w) (hsynth : sv w = some synthesizeChild) (hcache : CacheInvA L.O (cv w))
    (hr : RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-- **v10 from v9**: the checked wrapper's run gives the S3f2 entry's run from the same `w` (depth cell `ReadWorld`, `hcell.2.2.1.1`), and `Start` from the residual and the checks -/
theorem synth_hftPcieOutByte_finalOffCombined10 : HftFinalStmtOffCombined10 := by
  intro ι mref cref L mctx cctx w w' b D' hquiet hsynth hcache hr hcell hD hG hT hs h0
  exact synth_hftPcieOutByte_finalOffCombined9 L (start_of_residual L hr hquiet hsynth hcache)
    (entry2_of_pilotEntry3 hcell.2.2.1.1 hr) hcell hD hG hT hs h0

end Tools.ShippingFGCircuitS3jFinal

#print axioms Tools.ShippingFGCircuitS3jFinal.start_of_residual
#print axioms Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10
