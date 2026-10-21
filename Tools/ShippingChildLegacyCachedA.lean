import Tools.ShippingChildFallbackA
import Tools.ShippingChildKWalk
-- BUILT (unit A, round 2): b1-b3 exit 1 (print; the join point matched the cache discriminant twice), b4 exit 0. No `sorry`, no `axiom`, no `native_decide`, no new law / boundary
-- field. Law witness: `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only
-- (`FramedA.exprCacheGetIO` / `exprCacheModify` at the context's ref, whose provenance comes
-- from `CtxOk` through `KeepsCP.bindCtx`; `FramedA.sideModify .cacheHits`). No `RefLawsATele`.
/-! # `LegacyCachedA` from `LegacyImplA`

`Rec.translateExprToWireCached` (Elab.lean:7992-8028) is the cache shim around
`Rec.translateExprToWireImpl`: it reads `exprCache` from the compiler context
(`getCompilerState`; `KeepsCP.bindCtx` hands `CtxOk` of that context), looks the expression
up in `ref.get` (two `get?`), bumps `sparkleCacheHits`, calls the Impl, and inserts the result
with `ref.modify`. PROVED here: `translateExprToWireCachedA`, `legacyCachedA_of_impl`
(premise: `LegacyImplA O I` only, i.e. the Impl call is the hypothesis `himpl`). The join point
`__do_jp` (the Impl call and the insert) is walked at each of its three uses. -/
namespace Tools.ShippingChildLegacyCachedA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFresh

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

-- the join point: the Impl call, then the insert into the context's cache. Three uses: with the
-- cache discriminant already substituted (`none` / `some ref`, `hc` in context) or still open.
set_option hygiene false in
macro "cjp" : tactic => `(tactic|
  (refine KeepsCP.bind (himpl _ _ _ _) (fun r => ?_)
   refine KeepsCP.ite (fun _ => ?_) (fun _ => KeepsCP.pure _)
   first
   | (dsimp only; exact KeepsCP.pure _)
   | (dsimp only
      exact KeepsCP.bind (KeepsCP.lift (keepsA_framed O hA hS
        (FramedA.exprCacheModify _ _ (hcs _ hc)))) (fun _ => KeepsCP.pure _))
   | (cases hc : cs.exprCache with
      | none => dsimp only; exact KeepsCP.pure _
      | some ref =>
        dsimp only
        exact KeepsCP.bind (KeepsCP.lift (keepsA_framed O hA hS
          (FramedA.exprCacheModify ref _ (hcs ref hc)))) (fun _ => KeepsCP.pure _))))

section Cached
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- **The cache shim keeps `I`** given the Impl does. -/
theorem translateExprToWireCachedA (rec : TranslateFn)
    (himpl : ∀ e hint top named, KeepsCP mctx mref cctx cref I
      (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named) := by
  unfold Rec.translateExprToWireCached
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  try dsimp only
  refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
  · cases hc : cs.exprCache with
    | none => cjp
    | some ref =>
      have hr := hcs ref hc
      refine KeepsCP.bind (KeepsCP.lift ?_) (fun lr => ?_)
      · refine Keeps.bind (keepsA_framed O hA hS (FramedA.exprCacheGetIO ref hr)) (fun cache => ?_)
        try dsimp only
        split
        · exact Keeps.pure _
        · split
          · exact Keeps.pure _
          · exact Keeps.pure _
      · cases lr with
        | some w =>
          exact KeepsCP.bind (KeepsCP.lift (keepsA_framed O hA hS
            (FramedA.sideModify _ SideRef.cacheHits))) (fun _ => KeepsCP.pure _)
        | none => cjp
  · cjp

end Cached

/-- **`LegacyCachedA` from `LegacyImplA`**: the cache wrapper of the legacy translator. -/
theorem legacyCachedA_of_impl (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) (hImpl : LegacyImplA O I) : LegacyCachedA O I :=
  fun rec hrec mctx cctx hA e hint top named =>
    translateExprToWireCachedA O hA hS rec (hImpl rec hrec mctx cctx hA) e hint top named

end Tools.ShippingChildLegacyCachedA
