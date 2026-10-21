import Tools.ShippingChildLegacyHelpersA
-- UNBUILT (unit B, round 2): runs li1.. recorded in REPORT-B.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field.

namespace Tools.ShippingChildLegacyImplA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildWalkA
open Tools.ShippingChildLegacyHelpersA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option vc.budgetMs 200000

section Impl
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I)
include O hS

/-- The applicative `map`'s inline mini-translator, recursive on the two operands of an
application: by induction on a bound of the expression's size, in every admissible context
(it runs under `withLocalDecl`). -/
theorem toIR_keepsCP_bound (wireS : String) (fvarId : FVarId) :
    ∀ (n : Nat) (e : Lean.Expr), sizeOf e < n →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e)
  | 0, _, h => by omega
  | n + 1, e, h => by
    intro mctx cctx hA
    have ih := fun e' (h' : sizeOf e' < n) (mctx : Meta.Context) (cctx : Core.Context)
      (hA : AdmCtx O.quiet mctx cctx) => toIR_keepsCP_bound wireS fvarId n e' h' mctx cctx hA
    unfold Rec.translateExprToWireImpl.toIR
    vca

@[keepsA] theorem toIR_keepsCP (wireS : String) (fvarId : FVarId) (e : Lean.Expr)
    (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e) :=
  toIR_keepsCP_bound O hS wireS fvarId (sizeOf e + 1) e (Nat.lt_succ_self _) mctx cctx hA

@[keepsA] theorem getPrim_keepsCP (e : Lean.Expr) (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I (Rec.getPrimitiveNameFromLambda e) := by
  induction e with
  | lam _ _ body _ _ ih => unfold Rec.getPrimitiveNameFromLambda; exact ih
  | _ => unfold Rec.getPrimitiveNameFromLambda; vca

end Impl

section Main
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I) (T : RefLawsATele O.quiet mref cref)
include hS T

/-- TRIAL: the body with the App dispatcher and `canonHardwareKey` as hypotheses. -/
theorem impl_trial (rec : TranslateFn) (hrec : RecA O I rec)
    (hApp : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ e hint named, KeepsCP mctx mref cctx cref I
        (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named))
    (hcanon : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a)) :
    RecA O I (fun e h t n => Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e h t n) := by
  intro mctx cctx hA e hint top named
  have hr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named) := hrec
  show KeepsCP mctx mref cctx cref I (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
  unfold Rec.translateExprToWireImpl
  vca

end Main

end Tools.ShippingChildLegacyImplA

#print axioms Tools.ShippingChildLegacyImplA.impl_trial
