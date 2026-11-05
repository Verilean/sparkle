import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyRules
import Tools.ShippingGen4FKidsLegacyRules
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH3 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 3: handlers that take the recursive translator (handleTupleProjections, handleBitVecOps, handleRegister, handleMux, handleMemory, handleCircuitMonad), walked by `swalkN` with `kwAll`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH3
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

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section H3
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (tr : TranslateFn)
  (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCS mctx mref cctx cref I (tr e hint top named))
include M hpp hS htr

theorem handleTupleProjectionsKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleTupleProjections tr e name args hint named) := by
  unfold Rec.handleTupleProjections
  kwAll

theorem handleBitVecOpsKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleBitVecOps tr e name args hint named) := by
  unfold Rec.handleBitVecOps
  kwAll

theorem handleRegisterKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleRegister tr e name args hint named) := by
  unfold Rec.handleRegister
  kwAll

theorem handleMuxKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleMux tr e name args hint named) := by
  unfold Rec.handleMux
  kwAll

theorem handleMemoryKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleMemory tr e name args hint named) := by
  unfold Rec.handleMemory
  kwAll

theorem handleCircuitMonadKS (hA : AdmCtx O.quiet mctx cctx)
    (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (Rec.handleCircuitMonad tr e name args hint named) := by
  unfold Rec.handleCircuitMonad
  kwAll

end H3

end Tools.ShippingGen4FKidsLegacyH3
