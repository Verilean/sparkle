import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH6
import Tools.ShippingGen4FKidsLegacyH6
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH7 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 7: the inline attempt `tryInlineUnfold` as a `TripleCP` (copy of `tryInlineUnfold_tripleCP`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH7
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

section H7
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCS mctx mref cctx cref I (tr e hint top named))
include M hpp hS htr

/-- **The inline attempt's result**: the invariant is kept, and the exception it returns (its second
component) is none or an exception in the class (copy of `tryInlineUnfold_tripleCP`). -/
theorem tryInlineUnfold_tripleCPKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (named : Bool) :
    TripleCP mctx mref cctx cref I (Rec.tryInlineUnfold tr e hint named)
      (fun a w => I w ∧ OkOpt a.2) (fun e w => I w ∧ OkExc e) := by
  unfold Rec.tryInlineUnfold
  refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCS (by kwAll)) ?_
  intro eReduced
  refine TripleCP.ite (fun _ => ?_) (fun _ => TripleCP.pure fun _ hw => ⟨hw, OkOpt.none⟩)
  refine TripleCP.bind (Q := fun _ => I)
    (TripleCP.ofKeepsCS (snapshotWireCaches_keepsKS M hpp hS hA)) ?_
  intro saved
  refine TripleCP.tryCatchQ ?_ ?_
  · refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCS (htr _ _ hA _ _ _ _)) ?_
    intro w
    exact TripleCP.pure fun _ hw => ⟨hw, OkOpt.none⟩
  · intro ex1 h1
    refine TripleCP.bind (Q := fun _ => I)
      (TripleCP.ofKeepsCS (restoreWireCaches_keepsKS M hpp hS hA saved)) ?_
    intro _
    refine TripleCP.tryCatchQ ?_ ?_
    · refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCS (by kwAll)) ?_
      intro eReduced2
      refine TripleCP.ite (fun _ => ?_) (fun _ => TripleCP.pure fun _ hw => ⟨hw, OkOpt.some h1⟩)
      refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCS (htr _ _ hA _ _ _ _)) ?_
      intro w
      exact TripleCP.pure fun _ hw => ⟨hw, OkOpt.none⟩
    · intro ex2 h2
      refine TripleCP.bind (Q := fun _ => I)
        (TripleCP.ofKeepsCS (restoreWireCaches_keepsKS M hpp hS hA saved)) ?_
      intro _
      exact TripleCP.pure fun _ hw => ⟨hw, OkOpt.some h2⟩

end H7

end Tools.ShippingGen4FKidsLegacyH7
