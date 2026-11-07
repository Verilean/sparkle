import Tools.ShippingFGCircuitS2vLink
import Tools.ShippingFGCircuitS2tHftOb
set_option autoImplicit false
-- FG circuit pilot S2y: final statement v4 = v3 with `hcd` replaced by `EnvDefs/EnvCtors/RecFact` at (envAt cref w), carrier T. No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §48.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS2yFinal
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

/-- the carrier of `hftObCDT_T`: `CDT` in the empty closure environment -/
def cdvT : CDRel := fun env e α v => Tools.ShippingFGCircuitS2iDT.CDT env [] e α v

def HftFinalStmtOffCombined4 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hΔ : EnvDefs (envAt cref w) Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Delta) (hΓ : EnvCtors (envAt cref w) Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Gamma) (hrec : RecFact (envAt cref w))
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w)
    (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined4 : HftFinalStmtOffCombined4 := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hΔ hΓ hrec hadm hdown hD hG hT hs h0 hkgfacts
  exact synth_hftPcieOutByte_finalOffCombined3 cdvT Tools.ShippingFGCircuitS2oOb.HftObCDT (fun _ h => h) L lvl env₀ hstart hr hcell hchk hRdH hRdT
    (hftObCDT_T _ hΔ hΓ hrec) hadm hdown hD hG hT hs h0 hkgfacts

end Tools.ShippingFGCircuitS2yFinal

#print axioms Tools.ShippingFGCircuitS2yFinal.synth_hftPcieOutByte_finalOffCombined4
