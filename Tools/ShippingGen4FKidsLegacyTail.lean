import Tools.ShippingGen4KWalkEntryArms
import Tools.ShippingGen4FKidsEntryArms
import Tools.ShippingChildLegacyTailA
import Tools.ShippingGen4KWalkTac
import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen4FKidsHelpers
-- BUILT (PIECES ONLY: the legacy arm as a whole is NOT proved, see KWALK_PLAN S4 results): kjob lake build Tools.ShippingGen4KWalkLegacyTail exit 0 (rt169, source as of 9e5eb088); axioms standard only. Clean build is the coder's. S4 part 3 of scripts/gen4/KWALK_PLAN.md: the legacy arm of the entry for `KWalk` (copy of ShippingChildLegacyTailA 75-190, `StableK` / `MemoFamily` instead of `StableA` / `RefLawsATele`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. DIAG-PENDING hypothesis `LogMvKS` (see Entry).
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyTail
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
open Tools.ShippingGen4FKidsTac
open Tools.ShippingChildLegacyTailA
open Tools.ShippingChildLegacyHelpersA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4FKidsEntry
open Tools.ShippingGen4KWalkEntryArms
open Tools.ShippingGen4FKidsEntryArms
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingChildWalkA

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000

section Tail
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hS

theorem openRecordInputs_walk_keepsKS (body : Lean.Expr) (params : Array Lean.Expr)
    (inner : Lean.Expr) :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ idx binders subst opened,
      Keeps mctx mref cctx cref I
        (openRecordInputs.walk body params inner fuel idx binders subst opened)
  | 0, mctx, cctx, hA, idx, binders, subst, opened => by
    unfold openRecordInputs.walk
    swalkN [keepsK_throwErrorS M _ hS _ _]
  | fuel + 1, mctx, cctx, hA, idx, binders, subst, opened => by
    have ih : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ idx binders subst opened,
        Keeps mctx mref cctx cref I
          (openRecordInputs.walk body params inner fuel idx binders subst opened) :=
      fun mctx cctx hA => openRecordInputs_walk_keepsKS body params inner fuel mctx cctx hA
    unfold openRecordInputs.walk
    swalkN [keepsK_framedNM M _ hS (FramedNM.inferType _), keepsK_framedNM M _ hS (FramedNM.whnf _),
      keepsK_framedNM M _ hS (FramedNM.instantiateForall _ _),
      keepsK_framedNM M _ hS (FramedNM.mkLambdaFVars _ _ _ _ _ _ _),
      keepsK_getConstInfoInductS M _ hS _, keepsK_getConstInfoCtorS M _ hS _,
      keepsK_throwErrorS M _ hS _ _, M.tele.telescope I _ hS.1 hS.2 _ _, Keeps.tryCatch, Keeps.map _, Keeps.allMA,
      ih _ _ _ _ _ _ _]

theorem openRecordInputs_keepsKS (hA : AdmCtx O.quiet mctx cctx) (body : Lean.Expr) :
    Keeps mctx mref cctx cref I (openRecordInputs body) := by
  have hw := openRecordInputs_walk_keepsKS M hS body
  unfold openRecordInputs
  swalkN [keepsK_framedNM M _ hS (FramedNM.inferType _), M.tele.telescope I _ hS.1 hS.2 _ _,
    hw _ _ _ _ _ _ _ _ _ _]

theorem splitReturnLeavesStep_keepsKS :
    ∀ (rec : Lean.Expr → Option String → MetaM (Array (String × Lean.Expr))),
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (rec a b)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (splitReturnLeavesStep rec a b) := by
  intro rec hrec mctx cctx hA e p
  unfold splitReturnLeavesStep
  swalkN [keepsK_framedNM M _ hS (FramedNM.inferType _), keepsK_framedNM M _ hS (FramedNM.whnf _),
    keepsK_framedNM M _ hS (FramedNM.mkAppM _ _),
    keepsK_framedNM M _ hS (FramedNM.mkLambdaFVars _ _ _ _ _ _ _),
    keepsK_getConstInfoInductS M _ hS _, keepsK_getConstInfoCtorS M _ hS _, keepsK_getUserNameS M _ hS _,
    M.tele.telescope I _ hS.1 hS.2 _ _, M.tele.lamTelescope I _ hS.1 hS.2 _ _ _,
    Keeps.tryCatch, Keeps.map _, Keeps.arrayMapMA, Keeps.mapM]

theorem splitReturnLeaves_keepsKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr)
    (p : Option String) : Keeps mctx mref cctx cref I (splitReturnLeaves e p) :=
  fuelFixM2_keepsA splitReturnLeavesStep (splitReturnLeavesStep_keepsKS M hS) _ mctx cctx hA e p

end Tail

section Tail2
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

theorem bindInputsLegacyKPS (hA : AdmCtx O.quiet mctx cctx) (parameters : List (String × Nat))
    (symbolicMode : Bool) (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KeepsCS mctx mref cctx cref I k) (i : Nat) :
    KeepsCS mctx mref cctx cref I (bindInputsLegacy parameters symbolicMode xs i k) := by
  by_cases h : i < xs.size
  · have ih := bindInputsLegacyKPS hA parameters symbolicMode xs k hk (i + 1)
    unfold bindInputsLegacy
    rw [dif_pos h]
    swalkN [keepsK_getDeclS M hpp hS _ _, keepsK_throwErrorS M _ hS _ _,
      isSignalBinderTypeKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
      withDimVarMappingPS M hpp hS _ _ _, bindInputPortKPS M _ hS _ _ _ _, KeepsCS.tryCatch]
  · unfold bindInputsLegacy
    rw [dif_neg h]
    exact hk
termination_by xs.size - i
decreasing_by omega

end Tail2

end Tools.ShippingGen4FKidsLegacyTail
