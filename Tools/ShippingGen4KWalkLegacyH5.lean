import Tools.ShippingGen4KWalkLegacyH3
-- NOT BUILT (rt174 draft). LegacyImplK part 5: handleApplicative (+ `lower`), translateShiftAmount, walked by `kwalkN` with `kwAll`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH5
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
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkProjField

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H5
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (tr e hint top named))
include M hpp hS htr

theorem lowerK (hint : String) (named : Bool) :
    ∀ (signals : List Lean.Expr) (mctx : Meta.Context) (cctx : Core.Context),
      AdmCtx O.quiet mctx cctx → ∀ (f : Lean.Expr),
      KeepsCP mctx mref cctx cref I (Rec.handleApplicative.lower tr hint named f signals)
  | [], mctx, cctx, hA, f => by unfold Rec.handleApplicative.lower; kwAll
  | sig :: rest, mctx, cctx, hA, f => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) f => lowerK hint named rest mctx cctx hA f
    unfold Rec.handleApplicative.lower
    kwAll

theorem handleApplicativeK (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleApplicative tr e name args hint named) := by
  unfold Rec.handleApplicative
  have hl := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) signals f =>
    lowerK M hpp hS tr htr hint named signals mctx cctx hA f
  kwAll

theorem translateShiftAmountK (hA : AdmCtx O.quiet mctx cctx)
    (e e2 : Lean.Expr) (hint : String) :
    KeepsCP mctx mref cctx cref I (Rec.translateShiftAmount tr e e2 hint) := by
  unfold Rec.translateShiftAmount
  kwAll

end H5

end Tools.ShippingGen4KWalkLegacyH5
