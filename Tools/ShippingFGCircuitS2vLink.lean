import Tools.ShippingFGCircuitS2rFinal
import Tools.ShippingFGCircuitS2kLink
set_option autoImplicit false
-- FG circuit pilot S2v: `HftRootLink` is PROVED (`Tools.ShippingFGCircuitS2kLink.hftRootLink`), so the combined final statement v2 loses its `hlink` binder: `HftFinalStmtOffCombined3` (18 explicit hypotheses). Also `root_states`: the chain endpoint's `machine_states` specialised to the root with the fused state as an abstract stream. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §46.

namespace Tools.ShippingFGCircuitS2vLink
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

/-- **`HftFinalStmtOffCombined3`**: `HftFinalStmtOffCombined2` with the first binder `hlink : HftRootLink` REMOVED (it is now a theorem, `hftRootLink`). Binders: `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hadm hdown hD hG hT hs h0 hkgfacts` (18 explicit). -/
def HftFinalStmtOffCombined3 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w)
    (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined3 (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffCombined3 Ob CV := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hadm hdown hD hG hT hs h0 hkgfacts
  exact synth_hftPcieOutByte_finalOffCombined2 CV Ob hOb Tools.ShippingFGCircuitS2kLink.hftRootLink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hadm hdown hD hG hT hs h0 hkgfacts

theorem synth_hftPcieOutByte_finalOffCombined3_Z : HftFinalStmtOffCombined3 HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffCombined3 cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffCombined3_Y : HftFinalStmtOffCombined3 HftObCDY cdvY := synth_hftPcieOutByte_finalOffCombined3 cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffCombined3_X : HftFinalStmtOffCombined3 HftObCDX cdvX := synth_hftPcieOutByte_finalOffCombined3 cdvX _ (fun _ h => h)


section States
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core.Signal
open Tools.ShippingMachineTeleStates (teleState)
open Tools.ShippingMachineTele Tools.ShippingMachineTeleNest
open Tools.ShippingMachineNest (happendT castSS)
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto

/-- the fused state's slot list is the enclosing registers then the chain's -/
theorem root_hss : [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss := rfl

/-- **`machine_states` of the root, specialised**: for every inputs there are the Lean state signals `S₂` (the enclosing registers) and `Ss` (the chain's), and a state stream `X` (the fused state at each cycle: `teleState machineInners … t`) that starts at the reset tuple of the root and its chain, steps by the data's `nexts` over the Lean extension `machineExt`, and shows the data's `outs` as the declaration's observation `machineSource`. -/
theorem root_states (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) :
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6]))) (Ss : Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits))
      (X : Nat → HList (tys synth_hftPcieOutByte.machineData.ss)),
      (∀ t, X t = teleState synth_hftPcieOutByte.machineInners
        root_hss i bools bits S₂ Ss t) ∧
      X 0 = castSS root_hss
        (happendT [SType.bits 6] synth_hftPcieOutByte.machineInners.sss synth_hftPcieOutByte.machineInits synth_hftPcieOutByte.machineInners.initsT) ∧
      (∀ t, X (t + 1) = evalTerms
        (fun j => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos j))
        (fun j w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos j) w) synth_hftPcieOutByte.machineData.nexts) ∧
      ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f t) = synth_hftPcieOutByte.machineData.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos k))
        (fun k w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos k) w) o.2) :=
by
  obtain ⟨S₂, Ss, X, hX, h0, hstep, hobs⟩ := Tools.ShippingFGCircuitS2kLink.states_abs
    (src := fun i b bi => synth_hftPcieOutByte.machineSource i b bi) _ _ _ _ i bools bits
    (synth_hftPcieOutByte.machine_states i bools bits)
  exact ⟨S₂, Ss, X, hX, h0, hstep, hobs⟩

end States

end Tools.ShippingFGCircuitS2vLink

#print axioms Tools.ShippingFGCircuitS2vLink.synth_hftPcieOutByte_finalOffCombined3_Z
#print axioms Tools.ShippingFGCircuitS2vLink.synth_hftPcieOutByte_finalOffCombined3_Y
#print axioms Tools.ShippingFGCircuitS2vLink.synth_hftPcieOutByte_finalOffCombined3_X
#print axioms Tools.ShippingFGCircuitS2vLink.root_states
