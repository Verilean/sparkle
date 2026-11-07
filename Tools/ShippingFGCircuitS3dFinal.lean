import Tools.ShippingFGCircuitS3cFinal
import Tools.ShippingFGCircuitS3b2Final
set_option autoImplicit false
-- FG circuit pilot S3d: final statement v8 = v7r (pilot entry, lvl₀, no lvl/hreadH/hreadT) WITHOUT hadm and hdown, hT at TeleRX (as v7). Route: offR_to_off, then v7 at lvl := lvl₀ with hreadH/hreadT from pilotReaderOk_sound + readerOk_of_run. No premise beyond v7r ∪ v7. docs/FG-CIRCUIT-PILOT.md §54. No sorry/axiom/native_decide/TRUSTED/law.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3dFinal
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
open Tools.ShippingFGCircuitS3b2Reader (lvl₀)
open Tools.ShippingFGCircuitS3b2Final (pilotReaderOk pilotReaderOk_sound readerOk_of_run)
open Tools.ShippingFGCircuitS3b2Core (offR_to_off)
open Tools.ShippingFGCircuitS3cFinal (synth_hftPcieOutByte_finalOffCombined7)

/-- **v8** (11 binders): the pilot entry (`hr` is a run of `synthesizeCombinationalOffR pilotReaderOk hftRoot`) at the concrete `lvl₀` (in `hchk` and in the conclusion's `GPt`), WITHOUT `lvl hreadH hreadT hadm hdown`; `hT` is `TeleRX` as in v7 -/
def HftFinalStmtOffCombined8 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOffR pilotReaderOk hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl₀ env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined8 : HftFinalStmtOffCombined8 := by
  intro ι mref cref L env₀ mctx cctx w w' b D' hstart hr hcell hchk hD hG hT hs h0
  obtain ⟨-, hH, hT'⟩ := pilotReaderOk_sound (readerOk_of_run hcell hr)
  exact synth_hftPcieOutByte_finalOffCombined7 L lvl₀ env₀ hstart (offR_to_off hr) hcell hchk hH hT' hD hG hT hs h0

end Tools.ShippingFGCircuitS3dFinal

#print axioms Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8
