import Tools.ShippingGen4KWalkProjField
import Tools.ShippingGen4KWalkCanon
-- NOT BUILT. S3 (part 5) of scripts/gen4/KWALK_PLAN.md, frozen in scripts/gen4/KWALK_S3_FREEZE.md: the fallback assembled (one arm per `fallbackKind`) and the shipping translator for `StableK`
-- (copy of ShippingChildFallbackA 505-577). `canonHardwareKey` and `projFieldName?` are PROVED (Canon / ProjField files); the three REMAINING HYPOTHESES of `translateFallbackK` are
-- `LegacyImplK` (`Rec.translateExprToWireImpl`, not decomposed), `LegacyCachedK` (its cache wrapper) and `ChildEntryK` (`childSynthEntry`, the child recursion = S4-S6).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkFallback
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildKWalk
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4KWalkInst
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkCanon

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `Rec.translateExprToWireImpl` (the legacy translator's main body). HYPOTHESIS of `translateFallbackK`. -/
def LegacyImplK (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec, RecK O I rec →
    RecK O I (fun e h t n => Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e h t n)

/-- `Rec.translateExprToWireCached` (its cache wrapper). HYPOTHESIS of `translateFallbackK`. -/
def LegacyCachedK (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec, RecK O I rec →
    RecK O I (fun e h t n => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e h t n)

/-- `childSynthEntry` (the child recursion). HYPOTHESIS of `translateFallbackK`. -/
def ChildEntryK (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c)

/-- **The fallback, one arm per `fallbackKind`**, for `StableK`. -/
theorem translateFallbackK {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (tenv : Lean.Environment)
    (hImpl : LegacyImplK O I) (hCached : LegacyCachedK O I) (hchild : ChildEntryK O I)
    (rec : TranslateFn) (hrec : RecK O I rec) : RecK O I (translateFallback tenv rec) := by
  intro mctx cctx hA e hint top named
  have hr := hrec mctx cctx hA
  have hI := hImpl rec hrec mctx cctx hA
  have hC := hCached rec hrec mctx cctx hA
  unfold translateFallback
  try dsimp only
  split
  all_goals kwalk [translateControlCachedWithK M hA hS,
    (translateBoolUncachedWithK M hA hS rec hr _ (fun e h t n => hI e h t n)),
    translateVectorMuxUncachedWithK M hA hS rec hr, translateSetWidthUncachedWithK M hA hS rec hr,
    translateRegisterUncachedWithK M hA hS rec hr,
    translateRegisterEnableUncachedWithK M hA hS rec hr,
    translateLoopRegisterUncachedWithK M hA hS rec hr,
    translateCircuitDoUncachedWithK M hA hS rec hr,
    translateCircuitDo2UncachedWithK M hA hS rec hr,
    translateMemoryUncachedWithK M hA hS rec hr, translateSliceUncachedWithK M hA hS rec hr,
    translateConcatUncachedWithK M hA hS rec hr, translateConcatLitUncachedWithK M hA hS rec hr,
    translateSliceFUncachedWithK M hA hS rec hr,
    (translateInstanceOrFallbackK M hA hS rec hr tenv (hchild mctx cctx hA)
      (fun n s => projFieldNameK M hA hS n s) (fun a => canonHardwareKeyK M hA hS a)
      (fun e h t n => hC e h t n))]

/-- **The shipping translator keeps a `StableK` invariant**, in every admissible context and every
`CtxOk` compiler context, given exactly `LegacyImplK`, `LegacyCachedK`, `ChildEntryK`. -/
theorem translate_keepsK {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (tenv : Lean.Environment)
    (hImpl : LegacyImplK O I) (hCached : LegacyCachedK O I) (hchild : ChildEntryK O I) :
    RecK O I (fun e h t n => translateExprToWire tenv e h t n) :=
  translateK_of_fallback M hS tenv
    (fun rec hrec => translateFallbackK M hS tenv hImpl hCached hchild rec hrec)

end Tools.ShippingGen4KWalkFallback

#print axioms Tools.ShippingGen4KWalkFallback.translateFallbackK
#print axioms Tools.ShippingGen4KWalkFallback.translate_keepsK
