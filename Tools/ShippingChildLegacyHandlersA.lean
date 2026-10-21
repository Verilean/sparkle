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
  (hS : StableA O.quiet I) (T : RefLawsATele O.quiet mref cref)
  (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (tr e hint top named))
include O hS T htr

@[keepsA] theorem handleErrorPatterns_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleErrorPatterns e name args hint named) := by
  vca

@[keepsA] theorem handleTupleProjections_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleTupleProjections tr e name args hint named) := by
  vca

@[keepsA] theorem snapshotWireCaches_keepsCP (hA : AdmCtx O.quiet mctx cctx) :
    KeepsCP mctx mref cctx cref I snapshotWireCaches := by
  vca

@[keepsA] theorem restoreWireCaches_keepsCP (hA : AdmCtx O.quiet mctx cctx) (c : WireCaches) :
    KeepsCP mctx mref cctx cref I (restoreWireCaches c) := by
  vca

@[keepsA] theorem normSpine_keepsA :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (x : Lean.Expr), Keeps mctx mref cctx cref I (Rec.translateExprToWireApp.normSpine x fuel)
  | 0, mctx, cctx, hA, x => by unfold Rec.translateExprToWireApp.normSpine; vca
  | fuel + 1, mctx, cctx, hA, x => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) x => normSpine_keepsA fuel mctx cctx hA x
    unfold Rec.translateExprToWireApp.normSpine
    vca

@[keepsA] theorem lower_keepsCP (hint : String) (named : Bool) :
    ∀ (signals : List Lean.Expr) (mctx : Meta.Context) (cctx : Core.Context),
      AdmCtx O.quiet mctx cctx → ∀ (f : Lean.Expr),
      KeepsCP mctx mref cctx cref I (Rec.handleApplicative.lower tr hint named f signals)
  | [], mctx, cctx, hA, f => by unfold Rec.handleApplicative.lower; vca
  | sig :: rest, mctx, cctx, hA, f => by
    have ih := fun mctx cctx (hA : AdmCtx O.quiet mctx cctx) f => lower_keepsCP hint named rest mctx cctx hA f
    unfold Rec.handleApplicative.lower
    vca

@[keepsA] theorem handleApplicative_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleApplicative tr e name args hint named) := by
  vca

@[keepsA] theorem handleBitVecOps_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleBitVecOps tr e name args hint named) := by
  vca

@[keepsA] theorem handleRegister_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleRegister tr e name args hint named) := by
  vca

@[keepsA] theorem handleMux_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleMux tr e name args hint named) := by
  vca

@[keepsA] theorem handleMemory_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleMemory tr e name args hint named) := by
  vca

@[keepsA] theorem handleLoop_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleLoop tr e name args hint named) := by
  vca

@[keepsA] theorem handleCircuitMonad_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (Rec.handleCircuitMonad tr e name args hint named) := by
  vca

@[keepsA] theorem translateShiftAmount_keepsCP (hA : AdmCtx O.quiet mctx cctx)
    (e e2 : Lean.Expr) (hint : String) :
    KeepsCP mctx mref cctx cref I (Rec.translateShiftAmount tr e e2 hint) := by
  vca

end Handlers

end Tools.ShippingChildLegacyHandlersA
