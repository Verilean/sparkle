import Tools.ShippingChildLegacyHelpersA
-- UNBUILT (unit B, round 2): runs lw1.. recorded in REPORT-B.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field.

namespace Tools.ShippingChildLegacyHandlersA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildWalkA
open Tools.ShippingChildLegacyHelpersA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000

section Handlers
variable (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
  (hS : StableA O.quiet I) (TL : LocalDeclLawA O.quiet mref cref) (TLet : LetDeclLawA O.quiet mref cref)
  (TF : ForallTelescopeLawA O.quiet mref cref)
  (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (tr e hint top named))
  (hchild : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))
include O hS TL TLet htr

omit TL TLet tr htr in
@[keepsA] theorem handleErrorPatterns_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleErrorPatterns e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem handleTupleProjections_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleTupleProjections tr e name args hint named) := by
  vca

omit TL TLet tr htr in
@[keepsA] theorem snapshotWireCaches_keepsCP (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I snapshotWireCaches := by
  vca

omit TL TLet tr htr in
@[keepsA] theorem restoreWireCaches_keepsCP (hA : AdmCtx O.quiet mctx cctx) (c : WireCaches) :
    KeepsCP mctx mref cctx cref I (restoreWireCaches c) := by
  vca

omit TL TLet tr htr in
@[keepsA] theorem normSpine_keepsA :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (x : Lean.Expr), Keeps mctx mref cctx cref I (Rec.translateExprToWireApp.normSpine x fuel)
  | 0, mctx, cctx, hA, x => by unfold Rec.translateExprToWireApp.normSpine; vca
  | fuel + 1, mctx, cctx, hA, x => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) x => normSpine_keepsA fuel mctx cctx hA x
    unfold Rec.translateExprToWireApp.normSpine
    vca

omit TLet in
@[keepsA] theorem lower_keepsCP (hint : String) (named : Bool) :
    ∀ (signals : List Lean.Expr) (mctx : Meta.Context) (cctx : Core.Context),
      AdmCtx O.quiet mctx cctx → ∀ (f : Lean.Expr),
      KeepsCP mctx mref cctx cref I (Rec.handleApplicative.lower tr hint named f signals)
  | [], mctx, cctx, hA, f => by unfold Rec.handleApplicative.lower; vca
  | sig :: rest, mctx, cctx, hA, f => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) f => lower_keepsCP hint named rest mctx cctx hA f
    unfold Rec.handleApplicative.lower
    vca

omit TLet in
@[keepsA] theorem handleApplicative_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleApplicative tr e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem handleBitVecOps_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleBitVecOps tr e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem handleRegister_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleRegister tr e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem handleMux_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleMux tr e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem handleMemory_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleMemory tr e name args hint named) := by
  vca

omit TLet in
@[keepsA] theorem handleLoop_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleLoop tr e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem handleCircuitMonad_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleCircuitMonad tr e name args hint named) := by
  vca

omit TL TLet in
@[keepsA] theorem translateShiftAmount_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e e2 : Lean.Expr) (hint : String) :
    KeepsCP mctx mref cctx cref I (Rec.translateShiftAmount tr e e2 hint) := by
  vca

omit TL TLet in
/-- **The inline attempt's result**: the invariant is kept, and the exception it returns (its
second component) is none or an exception in the class — one a `catch` of this run handed over
(`Triple.tryCatchQ`). -/
theorem tryInlineUnfold_tripleCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (named : Bool) :
    TripleCP mctx mref cctx cref I (Rec.tryInlineUnfold tr e hint named)
      (fun a w => I w ∧ OkOpt a.2) (fun e w => I w ∧ OkExc e) := by
  unfold Rec.tryInlineUnfold
  refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCP (by vca)) ?_
  intro eReduced
  refine TripleCP.ite (fun _ => ?_) (fun _ => TripleCP.pure fun _ hw => ⟨hw, OkOpt.none⟩)
  refine TripleCP.bind (Q := fun _ => I)
    (TripleCP.ofKeepsCP (snapshotWireCaches_keepsCP O hS hA)) ?_
  intro saved
  refine TripleCP.tryCatchQ ?_ ?_
  · refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCP (htr _ _ hA _ _ _ _)) ?_
    intro w
    exact TripleCP.pure fun _ hw => ⟨hw, OkOpt.none⟩
  · intro ex1 h1
    refine TripleCP.bind (Q := fun _ => I)
      (TripleCP.ofKeepsCP (restoreWireCaches_keepsCP O hS hA saved)) ?_
    intro _
    refine TripleCP.tryCatchQ ?_ ?_
    · refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCP (by vca)) ?_
      intro eReduced2
      refine TripleCP.ite (fun _ => ?_) (fun _ => TripleCP.pure fun _ hw => ⟨hw, OkOpt.some h1⟩)
      refine TripleCP.bind (Q := fun _ => I) (TripleCP.ofKeepsCP (htr _ _ hA _ _ _ _)) ?_
      intro w
      exact TripleCP.pure fun _ hw => ⟨hw, OkOpt.none⟩
    · intro ex2 h2
      refine TripleCP.bind (Q := fun _ => I)
        (TripleCP.ofKeepsCP (restoreWireCaches_keepsCP O hS hA saved)) ?_
      intro _
      exact TripleCP.pure fun _ hw => ⟨hw, OkOpt.some h2⟩

omit TL TLet in
include hchild TF in
@[keepsA] theorem handleDefinitionUnfold_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleDefinitionUnfold tr e name args hint named) := by
  vca

omit TLet in
include hchild TF in
@[keepsA] theorem translateExprToWireApp_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.translateExprToWireApp tr e hint named) := by
  vca

end Handlers

end Tools.ShippingChildLegacyHandlersA
