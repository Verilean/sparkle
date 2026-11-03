import Tools.ShippingGen4KWalkPrims
-- NOT BUILT. S2 of scripts/gen4/KWALK_PLAN.md: T3 (`translateSignalPureLiteral?` / `translateCanonicalSignalBinary` / `translateCore` /
-- `translateStepWith`) and the fuel induction, with `StableK` instead of `StableA` (copies of ShippingChildTranslateA 399-525).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.

namespace Tools.ShippingGen4KWalkTranslate
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildPathA
open Tools.Assume.MemoFamily
open Tools.Assume.FramedACases
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Core
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem translateSignalPureLiteralK (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?
  split
  · refine KeepsCP.bind (makeWirePK M hA hS _ _ _) (fun _ => ?_)
    refine KeepsCP.bind (emitAssignP _ _) (fun _ => ?_)
    exact KeepsCP.pure _
  · exact KeepsCP.pure _

theorem translateCanonicalSignalBinaryK (rec : TranslateFn)
    (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
    (e : Lean.Expr) (op : Sparkle.IR.AST.Operator) (args : Array Lean.Expr) (hint : String)
    (named : Bool) (n : Nat) (hw : canonicalSignalBitVecWidth args = some n) :
    KeepsCP mctx mref cctx cref I
      (translateCanonicalSignalBinary rec e op args true true hint named) := by
  unfold translateCanonicalSignalBinary
  first | rw [hw] | simp only [hw]
  refine KeepsCP.bind (KeepsCP.pure _) (fun _ => ?_)
  refine KeepsCP.bind (makeWirePK M hA hS _ _ _) (fun _ => ?_)
  first
    | refine KeepsCP.bind (KeepsCP.ite (fun _ => hrec _ _ _ _) (fun h => (h rfl).elim))
        (fun _ => ?_)
    | refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  first
    | refine KeepsCP.bind (KeepsCP.ite (fun _ => hrec _ _ _ _) (fun h => (h rfl).elim))
        (fun _ => ?_)
    | refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (emitAssignP _ _) (fun _ => ?_)
  exact KeepsCP.pure _

theorem translateCoreK (rec : TranslateFn)
    (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateCore rec e hint top named) := by
  unfold translateCore
  split
  · exact lookupVarP _
  · split
    · refine KeepsCP.ite (fun _ => translateSignalPureLiteralK M hA hS _ _ _) (fun _ => ?_)
      split
      · refine KeepsCP.bind
          (translateCanonicalSignalBinaryK M hA hS rec hrec _ _ _ _ _ _ (by assumption))
          (fun _ => ?_)
        exact KeepsCP.pure _
      · exact KeepsCP.pure _
    · exact KeepsCP.pure _

theorem translateStepWithK (fallback : TranslateFn → TranslateFn) (rec : TranslateFn)
    (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
    (hfb : ∀ e hint top named, KeepsCP mctx mref cctx cref I (fallback rec e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateStepWith fallback rec e hint top named) := by
  unfold translateStepWith
  dsimp only
  refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
  · refine KeepsCP.bind (cacheLookupValidatedK M hA hS _) (fun x => ?_)
    cases x with
    | some w => exact KeepsCP.pure _
    | none =>
      refine KeepsCP.bind (translateCoreK M hA hS rec hrec _ _ _ _) (fun y => ?_)
      cases y with
      | some w =>
        exact KeepsCP.ite (fun _ => KeepsCP.pure _)
          (fun _ => KeepsCP.bind (recordTranslationK M hA hS _ _ _) (fun _ => KeepsCP.pure _))
      | none => exact hfb _ _ _ _
  · refine KeepsCP.bind (translateCoreK M hA hS rec hrec _ _ _ _) (fun y => ?_)
    cases y with
    | some w =>
      exact KeepsCP.ite (fun _ => KeepsCP.pure _)
        (fun _ => KeepsCP.bind (recordTranslationK M hA hS _ _ _) (fun _ => KeepsCP.pure _))
    | none => exact hfb _ _ _ _

end Core

/-! ## The fuel induction (`fuelFix_of` is generic: reused from TranslateA) -/

/-- The translator handed in as `rec` keeps `I` in every ADMISSIBLE context. -/
def RecK (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) (rec : TranslateFn) :
    Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named)

theorem fuelZeroK (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop)
    (step : TranslateFn → TranslateFn) : RecK O I (translateFuelFix step 0) := by
  intro mctx cctx _ e hint top named
  unfold translateFuelFix
  exact KeepsCP.throw (Exception.error .missing "translation fuel exhausted") (by okmsg)

/-- **The translator from its fallback**, K version: if the fallback keeps `I` whenever its recursive
argument does (`RecK`), the shipping translator does. -/
theorem translateK_of_fallback {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (tenv : Lean.Environment)
    (hF : ∀ rec, RecK O I rec → RecK O I (translateFallback tenv rec)) :
    RecK O I (fun e h t n => translateExprToWire tenv e h t n) := by
  have hfix : RecK O I (translateFuelFix (translateStep tenv) translateFuelLimit) := by
    refine fuelFix_of (P := RecK O I) (translateStep tenv) (fuelZeroK O I _) ?_ _
    intro rec hrec mctx cctx hA e hint top named
    unfold translateStep
    exact translateStepWithK M hA hS (translateFallback tenv) rec (hrec mctx cctx hA)
      (hF rec hrec mctx cctx hA) e hint top named
  intro mctx cctx hA e hint top named
  first
    | exact hfix mctx cctx hA e hint top named
    | (unfold translateExprToWire; exact hfix mctx cctx hA e hint top named)

end Tools.ShippingGen4KWalkTranslate

#print axioms Tools.ShippingGen4KWalkTranslate.translateStepWithK
#print axioms Tools.ShippingGen4KWalkTranslate.translateK_of_fallback
