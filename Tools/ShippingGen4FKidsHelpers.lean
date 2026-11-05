import Tools.ShippingGen4KWalkEntryArms
import Tools.ShippingGen4FKidsEntryArms
import Tools.ShippingChildLegacyTailA
import Tools.ShippingGen4KWalkTac
import Tools.ShippingGen4FKidsTac
-- BUILT: kjob lake build Tools.ShippingGen4KWalkHelpers exit 0 (rt169, source as of 9e5eb088); axioms standard only. Clean build is the coder's. S4 part 3a of scripts/gen4/KWALK_PLAN.md: the translator's helpers (`extractWidth`, `inferHWType`, `extractDimExpr`, `inferHWTypeWithDimensions`, `inferHWTypeFromSignal`, `isSignalBinderType`) for `StableK`
-- (copy of ShippingChildLegacyHelpersA, walked by `swalkN`). DIAG-PENDING hypothesis `PpMvKS` (one `ppExpr` leaves the memo as it was): the helpers render an error message with `ppExpr` (Elab.lean 681, 686, 715) before they `throwError`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom to the family. No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsHelpers
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
open Tools.ShippingChildWalkA
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

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **DIAG-PENDING HYPOTHESIS.** One `ppExpr` leaves the memo as it was, in a quiet world. -/
def PpMvKS (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ (e : Lean.Expr) w, O.quiet w →
    mv (endW mctx mref cctx cref (Lean.Meta.ppExpr e) w) = mv w

section H
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

theorem keepsK_ppExprS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (Lean.Meta.ppExpr e) := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.diag hA _ (Diag.ppExpr e) w hq
  have hm := hpp mctx cctx hA e w hq
  refine ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 hm (fun _ => hk.2) hw, ?_⟩
  unfold ErrOk
  cases hmm : (Lean.Meta.ppExpr e) mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e' w1 => exact O.excOk hA _ (.diag (Diag.ppExpr e)) w e' w1 hq hmm

theorem keepsK_getDeclS (hA : AdmCtx O.quiet mctx cctx) (id : FVarId) :
    Keeps mctx mref cctx cref I (id.getDecl : MetaM LocalDecl) := by
  unfold FVarId.getDecl
  refine Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) fun l => ?_
  cases l.find? id with
  | some d => exact Keeps.pure d
  | none => exact keepsK_framedNM M hA hS (FramedNM.fvarThrowUnknown id)

end H

section Steps
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hpp hS

set_option hygiene false in
macro "kwH" : tactic => `(tactic| swalkN [keepsK_framedNM M _ hS (FramedNM.whnf _),
  keepsK_framedNM M _ hS (FramedNM.inferType _), keepsK_framedNM M _ hS FramedNM.env,
  keepsK_framedNM M _ hS FramedNM.monoMs,
  keepsK_throwErrorS M _ hS _ _, keepsK_ppExprS M hpp hS _ _, keepsK_getDeclS M hpp hS _ _,
  Keeps.withReaderA (q := O.quiet) _ _])

theorem extractWidthStepKS (hA : AdmCtx O.quiet mctx cctx) (rec : Lean.Expr → MetaM Nat)
    (hrec : ∀ a, Keeps mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (extractWidthStep rec e) := by
  unfold extractWidthStep
  kwH

theorem extractWidthKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (extractWidth e) := by
  unfold extractWidth
  exact fuelFixM_keepsA extractWidthStep
    (fun rec hrec mctx cctx hA a => extractWidthStepKS M hpp hS hA rec (hrec mctx cctx hA) a) _ mctx cctx hA e

theorem inferHWTypeStepKS (hA : AdmCtx O.quiet mctx cctx) (rec : Lean.Expr → MetaM (Option Sparkle.IR.Type.HWType))
    (hrec : ∀ a, Keeps mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (inferHWTypeStep rec e) := by
  unfold inferHWTypeStep
  swalkN [keepsK_framedNM M _ hS (FramedNM.whnf _),
    keepsK_framedNM M _ hS (FramedNM.inferType _), keepsK_framedNM M _ hS FramedNM.env,
    Keeps.withReaderA (q := O.quiet) _ _, extractWidthKS M hpp hS _ _]

theorem inferHWTypeKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    Keeps mctx mref cctx cref I (inferHWType e) := by
  unfold inferHWType
  exact fuelFixM_keepsA inferHWTypeStep
    (fun rec hrec mctx cctx hA a => inferHWTypeStepKS M hpp hS hA rec (hrec mctx cctx hA) a) _ mctx cctx hA e

theorem extractDimExprStepKS (hA : AdmCtx O.quiet mctx cctx) (rec : Lean.Expr → CompilerM Sparkle.IR.Type.DimExpr)
    (hrec : ∀ a, KeepsCS mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractDimExprStep rec e) := by
  unfold extractDimExprStep
  swalkN [keepsK_framedNM M _ hS (FramedNM.whnf _), keepsK_throwErrorS M _ hS _ _, keepsK_ppExprS M hpp hS _ _,
    keepsK_getDeclS M hpp hS _ _]

theorem extractDimExprKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (extractDimExpr e) := by
  unfold extractDimExpr
  exact Tools.ShippingGen4FKidsCanon.KeepsCS.fuelFixM extractDimExprStep (fun rec hrec a => extractDimExprStepKS M hpp hS hA rec hrec a) _ e

theorem inferHWTypeWithDimensionsStepKS (hA : AdmCtx O.quiet mctx cctx)
    (rec : Lean.Expr → CompilerM (Option Sparkle.IR.Type.HWType))
    (hrec : ∀ a, KeepsCS mctx mref cctx cref I (rec a)) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (inferHWTypeWithDimensionsStep rec e) := by
  unfold inferHWTypeWithDimensionsStep
  swalkN [keepsK_framedNM M _ hS (FramedNM.whnf _), keepsK_throwErrorS M _ hS _ _, keepsK_ppExprS M hpp hS _ _,
    Keeps.withReaderA (q := O.quiet) _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _]

theorem inferHWTypeWithDimensionsKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (inferHWTypeWithDimensions e) := by
  unfold inferHWTypeWithDimensions
  exact Tools.ShippingGen4FKidsCanon.KeepsCS.fuelFixM inferHWTypeWithDimensionsStep (fun rec hrec a => inferHWTypeWithDimensionsStepKS M hpp hS hA rec hrec a) _ e

theorem inferHWTypeFromSignalKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (inferHWTypeFromSignal e) := by
  unfold inferHWTypeFromSignal
  swalkN [keepsK_framedNM M _ hS (FramedNM.whnf _), keepsK_framedNM M _ hS FramedNM.monoMs,
    keepsK_throwErrorS M _ hS _ _, inferHWTypeWithDimensionsKS M hpp hS _ _]

theorem isSignalBinderTypeKS (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (isSignalBinderType e) := by
  unfold isSignalBinderType
  swalkN [keepsK_framedNM M _ hS (FramedNM.whnf _)]

/-- `withDimVarMapping` keeps provenance (the update leaves `exprCache`). -/
theorem withDimVarMappingPS {α : Type} (fv : FVarId) (d : Sparkle.IR.Type.DimExpr)
    {k : CompilerM α} (hk : KeepsCS mctx mref cctx cref I k) :
    KeepsCS mctx mref cctx cref I (CompilerM.withDimVarMapping fv d k) := by
  unfold CompilerM.withDimVarMapping
  refine KeepsCS.bindCtx (fun old hold => ?_)
  refine KeepsCS.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

end Steps

end Tools.ShippingGen4FKidsHelpers
