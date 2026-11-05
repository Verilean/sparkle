import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH3
import Tools.ShippingGen4FKidsLegacyH3
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH5 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 5: handleApplicative (+ `lower`), translateShiftAmount, walked by `swalkN` with `kwAll`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH5
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
open Tools.ShippingGen4KWalkTac2
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4FKidsEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4FKidsLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4FKidsLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4FKidsCanon
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H5
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCS mctx mref cctx cref I (tr e hint top named))
include M hpp hS htr

theorem lowerKS (hint : String) (named : Bool) :
    ∀ (signals : List Lean.Expr) (mctx : Meta.Context) (cctx : Core.Context),
      AdmCtx O.quiet mctx cctx → ∀ (f : Lean.Expr),
      KeepsCS mctx mref cctx cref I (Rec.handleApplicative.lower tr hint named f signals)
  | [], mctx, cctx, hA, f => by unfold Rec.handleApplicative.lower; kwAll
  | sig :: rest, mctx, cctx, hA, f => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) f => lowerKS hint named rest mctx cctx hA f
    unfold Rec.handleApplicative.lower
    kwAll

theorem handleApplicativeKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleApplicative tr e name args hint named) := by
  unfold Rec.handleApplicative
  have hl := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) signals f =>
    lowerKS M hpp hS tr htr hint named signals mctx cctx hA f
  kwAll

theorem translateShiftAmountKS (hA : AdmCtx O.quiet mctx cctx)
    (e e2 : Lean.Expr) (hint : String) :
    KeepsCS mctx mref cctx cref I (Rec.translateShiftAmount tr e e2 hint) := by
  unfold Rec.translateShiftAmount
  kwAll

end H5

end Tools.ShippingGen4FKidsLegacyH5
