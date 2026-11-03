import Tools.ShippingGen4KWalkEntryArms
import Tools.ShippingChildLegacyTailA
import Tools.ShippingGen4KWalkTac
import Tools.ShippingGen4KWalkHelpers
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
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingChildWalkA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000

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

theorem openRecordInputs_keepsK (hA : AdmCtx O.quiet mctx cctx) (body : Lean.Expr) :
    Keeps mctx mref cctx cref I (openRecordInputs body) := by
  have hw := openRecordInputs_walk_keepsK M hS body
  unfold openRecordInputs
  kwalkM [keepsK_framedNM M _ hS (FramedNM.inferType _), M.tele.telescope I _ hS.1 hS.2 _ _,
    hw _ _ _ _ _ _ _ _ _ _]

theorem splitReturnLeavesStep_keepsK :
    ∀ (rec : Lean.Expr → Option String → MetaM (Array (String × Lean.Expr))),
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (rec a b)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ a b,
        Keeps mctx mref cctx cref I (splitReturnLeavesStep rec a b) := by
  intro rec hrec mctx cctx hA e p
  unfold splitReturnLeavesStep
  kwalkM [keepsK_framedNM M _ hS (FramedNM.inferType _), keepsK_framedNM M _ hS (FramedNM.whnf _),
    keepsK_framedNM M _ hS (FramedNM.mkAppM _ _),
    keepsK_framedNM M _ hS (FramedNM.mkLambdaFVars _ _ _ _ _ _ _),
    keepsK_getConstInfoInduct M _ hS _, keepsK_getConstInfoCtor M _ hS _, keepsK_getUserName M _ hS _,
    M.tele.telescope I _ hS.1 hS.2 _ _, M.tele.lamTelescope I _ hS.1 hS.2 _ _ _,
    Keeps.tryCatch, Keeps.map _, Keeps.arrayMapMA, Keeps.mapM]

theorem splitReturnLeaves_keepsK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr)
    (p : Option String) : Keeps mctx mref cctx cref I (splitReturnLeaves e p) :=
  fuelFixM2_keepsA splitReturnLeavesStep (splitReturnLeavesStep_keepsK M hS) _ mctx cctx hA e p

end Tail

section Tail2
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

theorem bindInputsLegacyKP (hA : AdmCtx O.quiet mctx cctx) (parameters : List (String × Nat))
    (symbolicMode : Bool) (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KeepsCP mctx mref cctx cref I k) (i : Nat) :
    KeepsCP mctx mref cctx cref I (bindInputsLegacy parameters symbolicMode xs i k) := by
  by_cases h : i < xs.size
  · have ih := bindInputsLegacyKP hA parameters symbolicMode xs k hk (i + 1)
    unfold bindInputsLegacy
    rw [dif_pos h]
    kwalkM [keepsK_getDecl M hpp hS _ _, keepsK_throwError M _ hS _ _,
      isSignalBinderTypeK M hpp hS _ _, inferHWTypeFromSignalK M hpp hS _ _,
      withDimVarMappingP M hpp hS _ _ _, bindInputPortKP M _ hS _ _ _ _, KeepsCP.tryCatch]
  · unfold bindInputsLegacy
    rw [dif_neg h]
    exact hk
termination_by xs.size - i
decreasing_by omega

end Tail2

end Tools.ShippingGen4KWalkLegacyTail
