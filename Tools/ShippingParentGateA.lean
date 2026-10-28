import Tools.ShippingGatePorts
import Tools.ShippingCallsGateA
import Tools.ShippingParentPortsA
-- BUILT (unit PH, par/u-ph): ph8 exit 0. See REPORT-PH.md.
-- SCOPE (binding): this file proves facts about the checks of the shipped module up to `designCheck = true`
-- (resp. the check statement named below), NOT a parent semantic-equivalence head and NOT the endpoint
-- `machine_design_svH_full` (its semantic part still takes `ChildBnd`: OPEN). Not runtime fit.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit PH: the child-side facts of a gate child, read off a `RealChildA`

`Tools.ShippingGatePorts.gate_real_ports` and `Tools.ShippingCombKidText.gate_real_kidK` unpack the old
`RealChild` with `h.inv`; here the same two facts are read off the run inside a `RealChildA O`
(`cases h with | run …`, as `Tools.ShippingCallsGateA.childFull_of_realA` does for `ChildFull`).
`RealChildA` is a history of a past synthesis run, not correctness in the current environment. -/

namespace Tools.ShippingParentGateA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingGatePorts Tools.ShippingCombKidText
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Sparkle.IR.OptCheck (seqStmtOk)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The common port facts of a gate child, from a `RealChildA`** (`gate_real_ports` on the new boundary). -/
theorem gate_real_portsA (O : RefLawsAOps MkRefd mref cref) {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) : GateChildPorts c bs srt.width y.1 := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact gate_child_ports hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old peel he hb hv

/-- **The children's text check of a gate child, from a `RealChildA`** (`gate_real_kidK` on the new boundary). -/
theorem gate_real_kidKA (O : RefLawsAOps MkRefd mref cref) {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    have hfc := gate_child_forwardCheck hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old
      peel he hb hv
    have hfull := gate_child_fullFacts hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old
      peel he hb hv
    obtain ⟨hall, h2, h3⟩ := forwardCheck_text hfc
    have hs : _ := Tools.ShippingMachineShipsComb.assigns_seqOk hall
    refine ⟨fun C n => Tools.ShippingLeafTyped.kidCheck_leaf_of_text C n hs h2 h3, ?_⟩
    intro g hg
    rw [hfull.design] at hg
    cases hg

end Tools.ShippingParentGateA
