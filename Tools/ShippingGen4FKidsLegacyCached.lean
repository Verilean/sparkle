import Tools.ShippingGen4FKidsEntry
import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkFallback
import Tools.ShippingGen4FKidsFallback
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyCached exit 0 (rt167, source as of de85ce20); axioms standard only. Clean build is the coder's. S3 (part 6) of scripts/gen4/KWALK_PLAN.md: `LegacyCachedKS` from `LegacyImplKS` (copy of ShippingChildLegacyCachedA), `StableK` instead of `StableA`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyCached
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4FKidsTranslate
open Tools.ShippingGen4KWalkFallback
open Tools.ShippingGen4FKidsFallback
open Tools.Assume.MemoFamily
open Tools.ShippingChildKWalk
open Tools.ShippingChildFresh

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele
open Tools.ShippingGen4FKidsEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

-- the join point: the Impl call, then the insert into the context's cache. Three uses: with the
-- cache discriminant already substituted (`none` / `some ref`, `hc` in context) or still open.
set_option hygiene false in
macro "cjpK" : tactic => `(tactic|
  (refine KeepsCS.bind (himpl _ _ _ _) (fun r => ?_)
   refine KeepsCS.ite (fun _ => ?_) (fun _ => KeepsCS.pure _)
   first
   | (dsimp only; exact KeepsCS.pure _)
   | (dsimp only
      exact KeepsCS.bind (KeepsCS.lift (keepsK_framedNM M hA hS
        (FramedNM.exprCacheModify _ _ (hcs _ hc)))) (fun _ => KeepsCS.pure _))
   | (cases hc : cs.exprCache with
      | none => dsimp only; exact KeepsCS.pure _
      | some ref =>
        dsimp only
        exact KeepsCS.bind (KeepsCS.lift (keepsK_framedNM M hA hS
          (FramedNM.exprCacheModify ref _ (hcs ref hc)))) (fun _ => KeepsCS.pure _))))

section Cached
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

/-- **The cache shim keeps `I`** given the Impl does. -/
theorem translateExprToWireCachedKS (rec : TranslateFn)
    (himpl : ∀ e hint top named, KeepsCS mctx mref cctx cref I
      (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCS mctx mref cctx cref I
      (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named) := by
  unfold Rec.translateExprToWireCached
  refine KeepsCS.bindCtx (fun cs hcs => ?_)
  try dsimp only
  refine KeepsCS.ite (fun _ => ?_) (fun _ => ?_)
  · cases hc : cs.exprCache with
    | none => cjpK
    | some ref =>
      have hr := hcs ref hc
      refine KeepsCS.bind (KeepsCS.lift ?_) (fun lr => ?_)
      · refine Keeps.bind (keepsK_framedNM M hA hS (FramedNM.exprCacheGetIO ref hr)) (fun cache => ?_)
        try dsimp only
        split
        · exact Keeps.pure _
        · split
          · exact Keeps.pure _
          · exact Keeps.pure _
      · cases lr with
        | some w =>
          exact KeepsCS.bind (KeepsCS.lift (keepsK_framedNM M hA hS
            (FramedNM.sideModify _ SideRefNM.cacheHits))) (fun _ => KeepsCS.pure _)
        | none => cjpK
  · cjpK

end Cached

/-- **`LegacyCachedKS` from `LegacyImplKS`**: the cache wrapper of the legacy translator. -/
theorem legacyCachedK_of_implS {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
    (hS : StableK O.quiet I) (hImpl : LegacyImplKS O I) : LegacyCachedKS O I :=
  fun rec hrec mctx cctx hA e hint top named =>
    translateExprToWireCachedKS M hA hS rec (hImpl rec hrec mctx cctx hA) e hint top named

end Tools.ShippingGen4FKidsLegacyCached

#print axioms Tools.ShippingGen4FKidsLegacyCached.legacyCachedK_of_implS
