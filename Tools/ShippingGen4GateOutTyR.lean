import Tools.ShippingGen4GateIfaceR
import Tools.ShippingGateKid
set_option autoImplicit false
-- NOT BUILT. U-GC0 (scripts/gen2/GATE_GC0_FREEZE.md): transfer of kjob/g4gate-g6 to base 15cd9d1f. No sorry / axiom / native_decide.

/-! # U-G2a, output side: `out : bitVector srt.width` for `srt.width ≠ 1` (supplier `gate_full_outputs`). Width 1: no supplier found, OPEN. -/

namespace Tools.ShippingGen2
open Sparkle.IR.Type (HWType)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)

variable {ι : Type}
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem gateLeaf_outTy (O : RefLawsAOps MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y)
    (hw1 : g.srt.width ≠ 1) :
    ∃ w : Nat, w = g.srt.width ∧ y.1.outputs = [{ name := "out", ty := .bitVector w }] := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact ⟨g.srt.width, rfl, Tools.ShippingGateKid.gate_full_outputs hr
      (Tools.ShippingReflectCtx.EntryDefines.ctx entry) g.old g.peel g.he g.hb g.hv hw1⟩

end Tools.ShippingGen2
