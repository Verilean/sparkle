import Tools.ShippingFGCircuitS2yFinal
import Tools.ShippingFGCircuitS2zFinal
import Tools.ShippingFGCircuitS3aKids
set_option autoImplicit false
-- FG circuit pilot S3a2: final statement v6 = v5 WITHOUT `hkgfacts`: it comes from the entry's check `startKidsOk hftRoot (envAt cref w) …` that a successful run passed. No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §50.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3aFinal
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

/-- **the run-level fact**: a successful run of the Off entry on the pilot root passed the callee check at ITS start environment `envAt cref w`
with the compiler's own `userInliner`/`instancePredicate`/`gatePeeledBody` at that environment (head, `getConstInfo` and `getEnv` keep the Core environment, as in `startEnvOk_of_run`). -/
theorem startKidsOk_of_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w') :
    Sparkle.Compiler.PilotKidTables.startKidsOk hftRoot (envAt cref w) (userInliner (envAt cref w)) (instancePredicate (envAt cref w)) gatePeeledBody = true := by
  obtain ⟨raw, D, w1', hcore, -⟩ := postEntryOff hr
  obtain ⟨s, w1, w2, w3, envR, ci, hh, hget, henv, hok⟩ := core_kidsOkOff hcore
  have e1 : envAt cref w1 = envAt cref w := headAtOff_of_cellPrem (w := w) hftRoot hcell s w1 hh
  have e2 : envAt cref w2 = envAt cref w1 := envFrame_getConstInfo hftRoot (getEnvFrame_of_cellPrem hcell) w1 ci w2 hget
  have e3 : envR = envAt cref w2 := Tools.ShippingEntryReadsLinked.getEnv_value henv
  rw [e3, e2, e1] at hok
  exact hok

/-- **v6**: the final statement v5 with `hkgfacts` REMOVED (derived from the run's own check `startKidsOk`, see `startKidsOk_of_run` and `Tools.ShippingFGCircuitS3aKids.startKidsOk_sound`); 16 binders -/
def HftFinalStmtOffCombined6 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined6 : HftFinalStmtOffCombined6 := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hadm hdown hD hG hT hs h0
  exact synth_hftPcieOutByte_finalOffCombined5 L lvl env₀ hstart hr hcell hchk hRdH hRdT hadm hdown hD hG hT hs h0
    (Tools.ShippingFGCircuitS3aKids.startKidsOk_sound (startKidsOk_of_run hcell hr))

end Tools.ShippingFGCircuitS3aFinal

#print axioms Tools.ShippingFGCircuitS3aFinal.startKidsOk_of_run
#print axioms Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6
