import Tools.ShippingFGCircuitS1uSrc
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmCallsGatePinned
import Tools.ShippingFGCircuitS2sAdmRunLocal
import Tools.ShippingFGCircuitS2sAdmLinked
import Tools.ShippingFGCircuitS2sAdmRunReads
import Tools.ShippingFGCircuitS2sAdmServedRealA
import Tools.ShippingFGCircuitS2sAdmParentRanA
import Tools.ShippingFGCircuitS2sAdmParentTailsA
import Tools.ShippingFGCircuitS2sAdmParentDesignA
import Tools.ShippingFGCircuitS2sAdmS1qLinked
import Tools.ShippingFGCircuitS2sAdmS1tFinal
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS1uSrc.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S1u: `hsrc` for the non-leaf root `synth_hftPcieOutByte`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §25.

/-! # S1u (part A): the generic `ExtStage` induction for a finite list of callees

`ExtStage Q g i bools bits S k` runs the first `k` calls of `g.d` over the callee table `Q`. `calleeOut` reads a callee package only through `q.d`, `q.kD` and `q.src`. So two tables that agree on those three
fields at every callee name give the same `ExtStage` at every stage (`ExtStage_agree_tables`, an induction on the stage). The package that `genGP` returns for the callee can therefore be replaced by the
callee's declaration-level observation, once the callee's own `src` is known. -/
namespace Tools.ShippingFGCircuitS1uSrc
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingGen5Sem Tools.ShippingGen2
open Tools.ShippingUnifiedSource (eval)

section Generic
variable {ι : Type} {dom : ι → DomainConfig}

end Generic
section Rec
variable {ι : Type} {dom : ι → DomainConfig}
open Tools.ShippingFGCircuitSrc (list_ext_of_map_eval)

end Rec
section Table
open Tools.ShippingGen5Acc Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingFGCircuitCover
open Tools.ShippingFGCircuitSrc (list_ext_of_map_eval)
variable {ι : Type} {dom : ι → DomainConfig}

end Table
section Hft
open Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuit (monoObs)
open Tools.ShippingFGCircuitCover Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingGen5Acc Tools.ShippingGen5DataOf
open Tools.ShippingGen5Sem (kDOf GenWF)

end Hft
section Final
open Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1qHead Tools.ShippingFGCircuitS1qLinked
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitCover Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitArtifact Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitBridge Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingStRefCorrespondence (ReadWorld)

def HftFinalStmtOffLX (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : StartX L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p


/-- **`synth_hftPcieOutByte_finalOffLX`**: S1t's assembly with `hsrc` supplied by `hftObSrc_of_rootLink` -/
theorem synth_hftPcieOutByte_finalOffLX (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLX Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hNoRaw
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact synth_hftPcieOutByte_finalOffX CV Ob hOb L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD
    (hftObSrc_of_rootLink hlink lvl (envAt cref w) hRead hRdH hRdT) hTop hNoRaw


theorem synth_hftPcieOutByte_finalOffL_ZX : HftFinalStmtOffLX HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLX cdvZ _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffL_YX : HftFinalStmtOffLX HftObCDY cdvY := synth_hftPcieOutByte_finalOffLX cdvY _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffL_XX : HftFinalStmtOffLX HftObCDX cdvX := synth_hftPcieOutByte_finalOffLX cdvX _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOffL_ofX (CV : CDRel) : HftFinalStmtOffLX (HftObOf CV) CV := synth_hftPcieOutByte_finalOffLX CV _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS1uSrc

#print axioms Tools.ShippingFGCircuitS1uSrc.ExtStage_agree_tables
#print axioms Tools.ShippingFGCircuitS1uSrc.genSemGen_src_eq_of_link
#print axioms Tools.ShippingFGCircuitS1uSrc.genGP_root_kids_src
#print axioms Tools.ShippingFGCircuitS1uSrc.hftObSrc_of_rootLink
#print axioms Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffLX
#print axioms Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffL_ZX

