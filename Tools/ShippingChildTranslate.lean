import Tools.ShippingChildHelpers

/-! # The translator keeps the child invariant, given its fallback does

`translateExprToWire` is `translateFuelFix translateStep translateFuelLimit`,
an ordinary definition: a fuel-bounded fixpoint of the non-recursive step
`translateStep = translateStepWith translateFallback`.

* **The fuel induction** (`fuelFix_keepsC`): if a step keeps the invariant
  whenever its recursive argument does, the fixpoint keeps it at every fuel, in every Meta and Core context (the
  handlers call the recursive argument under changed contexts) — at fuel 0
  it throws. Every outcome; the world, the compiler state and the
  circuit state are whatever the run reaches.
* **The step's own code** (`translateStepWith_keepsC`): the validated cache
  lookup, the core (`translateCore`: a bound variable, a `Signal.pure`
  literal, a canonical library operator with its two recursive operand
  translations), and the record of the result — walked, given the recursive
  argument and the fallback keep the invariant.

So `TranslateRel` follows from the same statement about `translateFallback`
alone (`translateRel_of_fallback`). -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The fallback, relative to the child entry and to the recursive
translator**: at any depth, in any contexts, IF the memoised child entry
keeps the invariant and the recursive argument `rec` does, a run of
`translateFallback rec` keeps it — on every outcome. -/
def FallbackRel (L : RefLaws mref cref) : Prop :=
  ∀ D, ChildKeeps L D → ∀ (rec : TranslateFn),
    (∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (rec e hint top named)) →
    ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (translateFallback rec e hint top named)

variable (L : RefLaws mref cref) (D : Nat)

/-- The validated cache lookup: the translation cache's read, the record's read. -/
@[keeps] theorem cacheLookupValidated_keepsC (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (cacheLookupValidated e) := by
  vc

/-- The record of a result, and the translation cache's update. -/
@[keeps] theorem recordTranslation_keepsC (e : Lean.Expr) (w : String) (cacheable : Bool) :
    KeepsC mctx mref cctx cref (J L D) (recordTranslation e w cacheable) := by
  vc

@[keeps] theorem makeWire_keepsC (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (CompilerM.makeWire hint ty named) :=
  keepsC_iff.mpr (makeWire_tripleC L D hint ty named)

@[keeps] theorem emitAssign_keepsC (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    KeepsC mctx mref cctx cref (J L D) (CompilerM.emitAssign lhs rhs) :=
  keepsC_iff.mpr (emitAssign_tripleC L D lhs rhs)

/-- **The core**: a bound variable, a `Signal.pure` literal, a canonical
library operator (two recursive operand translations, a wire, an assign). -/
@[keeps] theorem translateCore_keepsC (rec : TranslateFn)
    (hrec : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (rec e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateCore rec e hint top named) := by
  vc

/-- **One step of the knot**, given the recursive argument and the fallback. -/
theorem translateStepWith_keepsC (fallback : TranslateFn → TranslateFn) (rec : TranslateFn)
    (hrec : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (rec e hint top named))
    (hfb : ∀ e hint top named, KeepsC mctx mref cctx cref (J L D) (fallback rec e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (translateStepWith fallback rec e hint top named) := by
  vc

/-- **The fuel induction.** A step that keeps the invariant whenever its
recursive argument does gives a fixpoint that keeps it at every fuel. -/
theorem fuelFix_keepsC {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {I : Void IO.RealWorld → Prop}
    (step : TranslateFn → TranslateFn)
    (hstep : ∀ rec : TranslateFn,
      (∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
        KeepsC mctx mref cctx cref I (rec e hint top named)) →
      ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
        KeepsC mctx mref cctx cref I (step rec e hint top named)) :
    ∀ (k : Nat) (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref I (translateFuelFix step k e hint top named)
  | 0, mctx, cctx, e, hint, top, named => by
    unfold translateFuelFix
    exact KeepsC.throw _ (by okmsg)
  | k + 1, mctx, cctx, e, hint, top, named => by
    unfold translateFuelFix
    exact hstep _ (fuelFix_keepsC step hstep k) mctx cctx e hint top named

/-- **`TranslateRel` from `FallbackRel`.** -/
theorem translateRel_of_fallback (hF : FallbackRel L) : TranslateRel L := by
  intro D hC mctx cctx e hint top named
  unfold translateExprToWire
  refine fuelFix_keepsC translateStep (fun rec hrec mctx cctx e hint top named => ?_) _ mctx cctx
    e hint top named
  unfold translateStep
  exact translateStepWith_keepsC L D translateFallback rec hrec
    (hF D hC rec hrec mctx cctx) e hint top named

end Tools.ShippingChildInv
