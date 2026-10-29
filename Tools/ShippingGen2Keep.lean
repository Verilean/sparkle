import Tools.ShippingGen2Connect
import Tools.ShippingChildPinC
set_option autoImplicit false

/-! # Gen2 U0: G-KEEP-BODY at `InvAt` (GENERAL_SPEC.md §3.4)

`bodyKeepsP_of_tele` / `translate_keepsP_of_tele` (Tools/ShippingChildPinC.lean:314, :329) instantiated at `InvAt`
instead of `JQP`. Every component they use takes an arbitrary `StableA` invariant; the only invariant-specific facts
are `stableA_invAt` (Connect) and the synthesis-ref projection `h.1.1.2.1`. Result: `KeepBodyStmt` is PROVED.
G-KEEP-CHILD (the child entry, whose insertion needs `IHAt`) is NOT proved here. -/
namespace Tools.ShippingGen2
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildFresh
open Tools.ShippingChildCacheA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildDepthC
open Tools.ShippingChildCoreC
open Tools.ShippingChildComposeC
open Tools.ShippingChildPinC

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The synthesis ref holds `synthesizeChild` under `InvAt` (the projection `JQP` uses, `h.1.1.2.1`). -/
theorem invAt_sv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    ∀ w, InvAt L P Reach D w → sv w = some synthesizeChild :=
  fun _ h => h.1.1.2.1

/-- The translator keeps `InvAt D` from the child hook (`translate_keepsP_of_tele` at `InvAt`). -/
theorem translate_keepsInv_of_tele (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach D) (tenv : Lean.Environment) :
    RecA L.O (InvAt L P Reach D) (fun e h t n => translateExprToWire tenv e h t n) :=
  have hS := stableA_invAt L P Reach D
  have hchild : ChildEntryA L.O (InvAt L P Reach D) :=
    childEntryA_of_childSynthA L.O hS (invAt_sv L P Reach D) hC
  have hcanon : CanonKeyA L.O (InvAt L P Reach D) := Tools.ShippingChildCanonKeyA.canonKeyA L.O hS
  have hImpl : LegacyImplA L.O (InvAt L P Reach D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele L.O hS L.T hcanon hchild
  translate_keepsA L.O hS tenv hImpl
    (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl L.O hS hImpl) hcanon
    (Tools.ShippingChildProjFieldA.projFieldNameA L.O L.T hS) hchild

/-- **G-KEEP-BODY, PROVED**: the child hook at `D` gives the all-outcome keep of every synthesis body at `D`, on
every route (`bodyKeepsP_of_tele` at `InvAt`). -/
theorem keepBody (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : KeepBodyStmt L P Reach := by
  intro D hC
  have hS := stableA_invAt L P Reach D
  have hchild : ChildEntryA L.O (InvAt L P Reach D) :=
    childEntryA_of_childSynthA L.O hS (invAt_sv L P Reach D) hC
  have hcanon : CanonKeyA L.O (InvAt L P Reach D) := Tools.ShippingChildCanonKeyA.canonKeyA L.O hS
  have hImpl : LegacyImplA L.O (InvAt L P Reach D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele L.O hS L.T hcanon hchild
  exact fun mctx cctx hA declName tenv b ci isInst =>
    fromConst_frontends_of_handlers L.O hA hS hImpl
      (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl L.O hS hImpl) hcanon
      (Tools.ShippingChildProjFieldA.projFieldNameA L.O L.T hS) hC (invAt_sv L P Reach D)
      tenv b declName ci isInst
      (fun _ _ => Tools.ShippingChildLegacyTailA.legacyTailA_generic L.O L.T hS hA _
        (translate_keepsInv_of_tele L P Reach D hC tenv) b declName ci isInst)

end Tools.ShippingGen2
