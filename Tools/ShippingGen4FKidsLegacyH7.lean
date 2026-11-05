import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH6
import Tools.ShippingGen4FKidsLegacyH6
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH7 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 7: the inline attempt `tryInlineUnfold` as a `TripleCS` (copy of `tryInlineUnfold_tripleCP`).
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
open Tools.ShippingGen4FKidsEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false


/-! ## A result that carries a caught exception: its fact goes to the continuation (`KeepsCS` form)
`TripleCS`: the postcondition form of `KeepsCS` (from every `CtxOk` context and `StatePF` state; the final state is `GoodS`). -/

theorem triple_ofPre {α : Type} {P : Void IO.RealWorld → Prop} {φ : Prop}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop} {m : MetaM α}
    (h : φ → Triple mctx mref cctx cref P m Q R) :
    Triple mctx mref cctx cref (fun w => P w ∧ φ) m Q R :=
  fun w hw => h hw.2 w hw.1

def TripleCS (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α : Type} (P : Void IO.RealWorld → Prop)
    (c : CompilerM α) (Q : α → Void IO.RealWorld → Prop)
    (R : Exception → Void IO.RealWorld → Prop) : Prop :=
  ∀ (st : Sparkle.IR.Builder.CircuitState) (ctx : CompilerState), CtxOk ctx → StatePF st →
    Triple mctx mref cctx cref P (c ctx st) (fun p w => Q p.1 w ∧ GoodS st p.2) R

section TripleCSRules
variable {I : Void IO.RealWorld → Prop}

theorem TripleCS.ofKeepsCS {α : Type} {c : CompilerM α}
    (h : KeepsCS mctx mref cctx cref I c) :
    TripleCS mctx mref cctx cref I c (fun _ => I) (fun e w => I w ∧ OkExc e) :=
  fun st ctx hc hs => h st ctx hc hs

theorem TripleCS.pure {α : Type} {P : Void IO.RealWorld → Prop} {a : α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : ∀ w, P w → Q a w) :
    TripleCS mctx mref cctx cref P (Pure.pure a : CompilerM α) Q R :=
  fun st _ _ hs => Triple.pure (a := (a, st)) (fun w hw => ⟨h w hw, GoodS.refl hs⟩)

theorem TripleCS.bind {α β : Type} {P : Void IO.RealWorld → Prop} {c : CompilerM α}
    {f : α → CompilerM β} {Q : α → Void IO.RealWorld → Prop} {Q' : β → Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop}
    (h1 : TripleCS mctx mref cctx cref P c Q R)
    (h2 : ∀ a, TripleCS mctx mref cctx cref (Q a) (f a) Q' R) :
    TripleCS mctx mref cctx cref P (c >>= f) Q' R :=
  fun st ctx hc hs => Triple.bind (h1 st ctx hc hs) fun p => by
    obtain ⟨a, s⟩ := p
    exact triple_ofPre (φ := GoodS st s) (fun hg =>
      Triple.conseq (h2 a s ctx hc hg.2.1) (fun w hw => hw)
        (fun _ _ hh => ⟨hh.1, GoodS.trans hg hh.2⟩) (fun _ _ h => h))

theorem TripleCS.ite {α : Type} {c : Prop} [Decidable c] {P : Void IO.RealWorld → Prop}
    {a b : CompilerM α} {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (ha : c → TripleCS mctx mref cctx cref P a Q R) (hb : ¬c → TripleCS mctx mref cctx cref P b Q R) :
    TripleCS mctx mref cctx cref P (if c then a else b) Q R := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem TripleCS.tryCatchQ {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    {Q : α → Void IO.RealWorld → Prop}
    (hx : TripleCS mctx mref cctx cref I x Q (fun e w => I w ∧ OkExc e))
    (hh : ∀ e, OkExc e → TripleCS mctx mref cctx cref I (h e) Q (fun e w => I w ∧ OkExc e)) :
    TripleCS mctx mref cctx cref I (MonadExcept.tryCatch x h) Q (fun e w => I w ∧ OkExc e) :=
  fun st ctx hc hs => Triple.tryCatchQ (hx st ctx hc hs) fun e he => hh e he st ctx hc hs

theorem KeepsCS.bindCaught {σ β : Type}
    {c : CompilerM (σ × Option Exception)} {f : σ × Option Exception → CompilerM β}
    (h1 : TripleCS mctx mref cctx cref I c (fun a w => I w ∧ OkOpt a.2)
      (fun e w => I w ∧ OkExc e))
    (h2 : ∀ a, OkOpt a.2 → KeepsCS mctx mref cctx cref I (f a)) :
    KeepsCS mctx mref cctx cref I (c >>= f) :=
  fun st ctx hc hs => Triple.bind (h1 st ctx hc hs) fun p => by
    obtain ⟨a, s⟩ := p
    exact Triple.conseq (triple_ofPre (P := I) (φ := GoodS st s ∧ OkOpt a.2) (fun hg =>
      Triple.conseq (h2 a hg.2 s ctx hc hg.1.2.1) (fun w hw => hw)
        (fun _ _ hh => ⟨hh.1, GoodS.trans hg.1 hh.2⟩) (fun _ _ h => h)))
      (fun w hw => ⟨hw.1.1, hw.2, hw.1.2⟩) (fun _ _ h => h) (fun _ _ h => h)

end TripleCSRules

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
    TripleCS mctx mref cctx cref I (Rec.tryInlineUnfold tr e hint named)
      (fun a w => I w ∧ OkOpt a.2) (fun e w => I w ∧ OkExc e) := by
  unfold Rec.tryInlineUnfold
  refine TripleCS.bind (Q := fun _ => I) (TripleCS.ofKeepsCS (by kwAll)) ?_
  intro eReduced
  refine TripleCS.ite (fun _ => ?_) (fun _ => TripleCS.pure fun _ hw => ⟨hw, OkOpt.none⟩)
  refine TripleCS.bind (Q := fun _ => I)
    (TripleCS.ofKeepsCS (snapshotWireCaches_keepsKS M hpp hS hA)) ?_
  intro saved
  refine TripleCS.tryCatchQ ?_ ?_
  · refine TripleCS.bind (Q := fun _ => I) (TripleCS.ofKeepsCS (htr _ _ hA _ _ _ _)) ?_
    intro w
    exact TripleCS.pure fun _ hw => ⟨hw, OkOpt.none⟩
  · intro ex1 h1
    refine TripleCS.bind (Q := fun _ => I)
      (TripleCS.ofKeepsCS (restoreWireCaches_keepsKS M hpp hS hA saved)) ?_
    intro _
    refine TripleCS.tryCatchQ ?_ ?_
    · refine TripleCS.bind (Q := fun _ => I) (TripleCS.ofKeepsCS (by kwAll)) ?_
      intro eReduced2
      refine TripleCS.ite (fun _ => ?_) (fun _ => TripleCS.pure fun _ hw => ⟨hw, OkOpt.some h1⟩)
      refine TripleCS.bind (Q := fun _ => I) (TripleCS.ofKeepsCS (htr _ _ hA _ _ _ _)) ?_
      intro w
      exact TripleCS.pure fun _ hw => ⟨hw, OkOpt.none⟩
    · intro ex2 h2
      refine TripleCS.bind (Q := fun _ => I)
        (TripleCS.ofKeepsCS (restoreWireCaches_keepsKS M hpp hS hA saved)) ?_
      intro _
      exact TripleCS.pure fun _ hw => ⟨hw, OkOpt.some h2⟩

end H7

end Tools.ShippingGen4FKidsLegacyH7
