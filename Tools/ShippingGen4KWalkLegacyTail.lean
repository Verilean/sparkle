import Tools.ShippingGen4KWalkEntryArms
import Tools.ShippingChildLegacyTailA
import Tools.ShippingGen4KWalkTac
-- NOT BUILT (rt169). S4 part 3 of scripts/gen4/KWALK_PLAN.md: the legacy arm of the entry for `KWalk` (copy of ShippingChildLegacyTailA 75-190, `StableK` / `MemoFamily` instead of `StableA` / `RefLawsATele`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. DIAG-PENDING hypothesis `LogMvK` (see Entry).
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyTail
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4KWalkTac
open Tools.ShippingChildLegacyTailA
open Tools.ShippingChildLegacyHelpersA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryArms

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Tail
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hS

theorem openRecordInputs_walk_keepsK (body : Lean.Expr) (params : Array Lean.Expr)
    (inner : Lean.Expr) :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ idx binders subst opened,
      Keeps mctx mref cctx cref I
        (openRecordInputs.walk body params inner fuel idx binders subst opened)
  | 0, mctx, cctx, hA, idx, binders, subst, opened => by
    unfold openRecordInputs.walk
    kwalkM [keepsK_throwError M _ hS _ _]
  | fuel + 1, mctx, cctx, hA, idx, binders, subst, opened => by
    have ih : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ idx binders subst opened,
        Keeps mctx mref cctx cref I
          (openRecordInputs.walk body params inner fuel idx binders subst opened) :=
      fun mctx cctx hA => openRecordInputs_walk_keepsK body params inner fuel mctx cctx hA
    unfold openRecordInputs.walk
    kwalkM [keepsK_framedNM M _ hS (FramedNM.inferType _), keepsK_framedNM M _ hS (FramedNM.whnf _),
      keepsK_framedNM M _ hS (FramedNM.instantiateForall _ _),
      keepsK_framedNM M _ hS (FramedNM.mkLambdaFVars _ _ _ _ _ _ _),
      keepsK_getConstInfoInduct M _ hS _, keepsK_getConstInfoCtor M _ hS _,
      keepsK_throwError M _ hS _ _, M.tele.telescope I _ hS.1 hS.2 _ _, Keeps.tryCatch, Keeps.map _, Keeps.allMA,
      ih _ _ _ _ _ _ _]

end Tail

end Tools.ShippingGen4KWalkLegacyTail
