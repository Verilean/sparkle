import Tools.ShippingFGCircuitS2mReach2
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
import Tools.ShippingFGCircuitS2sAdmS1uSrc
import Tools.ShippingFGCircuitS2sAdmS1zClose
import Tools.ShippingFGCircuitS2sAdmS2dKids
import Tools.ShippingFGCircuitS2sAdmS2hHist3
import Tools.ShippingFGCircuitS2sAdmS2mReach
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS2mReach2.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S2m (part 2): the invariant `JQHR` (= `JQH` over `ropsR`), its establishment at the head of the root run, its preservation by the steps of the main induction, the miss premise derived from it, and `hftCoreCloses_of_kidsR`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §39.

namespace Tools.ShippingFGCircuitS2mReach
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Res)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (ReadsAt readsAt_self)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingEntryReadsLinked (CoreSaved)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## the profile lookup along the reached worlds -/

/-- the profile lookup is unset at every reached world, from the root fact and the leaf-step frame -/
theorem profOffW_of_reachedX {O : RefLawsAOpsX MkRefd mref cref} {w₀ : Void IO.RealWorld}
    (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀) {w : Void IO.RealWorld}
    (hr : ReachedX O.quiet O.adm mref cref w₀ w) : ProfOffW mref cref w := by
  induction hr with
  | start => exact h0
  | step hr' hl ih => exact hs _ _ hr' hl ih

/-! ## the invariant `JQHRX` -/


/-- **`JQHRX`**: the history invariant `JQHX` over the strengthened operations bundle `ropsRX`. A `JQHRX` world is quiet, reads `e = envAt cref w₀`, is reached from the root start world `w₀`; its cache entries carry the saved reads of the runs that created them. -/
def JQHRX (O : RefLawsAOpsX MkRefd mref cref) (hcell : CellPrem MkRefd mref cref) (e : Environment)
    (w₀ : Void IO.RealWorld) (hD : DRowEnvRX O e w₀) (hG : DiagEnvRX O e w₀)
    (D : Nat) (w : Void IO.RealWorld) : Prop :=
  JQHX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) D w


/-- what a `JQHRX` world says about its environment, its reach and its profile lookup -/
theorem jqhr_factsX {O : RefLawsAOpsX MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : Void IO.RealWorld} {hD : DRowEnvRX O e w₀} {hG : DiagEnvRX O e w₀}
    (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀) {D : Nat} {w : Void IO.RealWorld}
    (hw : JQHRX O hcell e w₀ hD hG D w) :
    O.quiet w ∧ ReadsAt e cref w ∧ ReachedX O.quiet O.adm mref cref w₀ w ∧ ProfOffW mref cref w :=
  ⟨hw.1.1.1, hw.1.1.2.1, hw.1.1.2.2, profOffW_of_reachedX h0 hs hw.1.1.2.2⟩


/-- **The miss premise from the invariant** (replaces S2h's universal `MissEX`): in a `JQHRX` world the evidence `KidEv e` for the call's context pair holds — `ReadsAt e` because the world's quiet predicate carries it, the profile lookup because the world is reached from `w₀` and the lookup is unset along the leaf steps. Nothing is asked of a world outside the invariant. -/
theorem missRX {O : RefLawsAOpsX MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : Void IO.RealWorld} {hD : DRowEnvRX O e w₀} {hG : DiagEnvRX O e w₀}
    (h0 : ProfOffW mref cref w₀) (hs : ProfStepRX O w₀) :
    MissEX (ropsRX O hcell e w₀ hD hG) (KidEv mref cref e) := by
  intro mctx cctx _ D _ n w hw _
  have hf := jqhr_factsX (hcell := hcell) (hD := hD) (hG := hG) h0 hs (D := D) (w := w) hw
  exact ⟨hf.2.1, hf.2.2.2 mctx cctx⟩

/-! ## establishment at the head of the root run, and the steps of the induction -/


/-- **Established at the head of the root run**: the start world is `JQHRX` at depth 0 (`ReadsAt (envAt cref w₀) w₀` is `readsAt_self`, `ReachedX.start`), and the head `coreHeadOff` (depth-0 branch: clears the cache) leaves a `JQHRX` world at depth 1. -/
theorem jqhr_headX {O : RefLawsAOpsX MkRefd mref cref} {hcell : CellPrem MkRefd mref cref}
    {w₀ : Void IO.RealWorld} {hD : DRowEnvRX O (envAt cref w₀) w₀} {hG : DiagEnvRX O (envAt cref w₀) w₀}
    (hadm : O.adm mctx cctx)
    (hjq : JQ O.quiet 0 w₀) {X : Name} {w1 : Void IO.RealWorld} {s : CoreSaved}
    (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w₀ s w1) :
    JQHRX O hcell (envAt cref w₀) w₀ hD hG (0 + 1) w1 :=
  coreHeadOff_jqhAX (E := KidEv mref cref (envAt cref w₀)) (ropsRX O hcell (envAt cref w₀) w₀ hD hG)
    hadm ⟨⟨hjq.1, readsAt_self cref w₀, .start⟩, hjq.2⟩ hh

end Tools.ShippingFGCircuitS2mReach

