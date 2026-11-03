import Tools.ShippingGen4KWalkTranslate
import Tools.ShippingChildKWalk
-- BUILT: kjob lake build Tools.ShippingGen4KWalkEmit exit 0 (rt167, source as of de85ce20); axioms standard only. Clean build is the coder's. S3 (part 1) of scripts/gen4/KWALK_PLAN.md, frozen in scripts/gen4/KWALK_S3_FREEZE.md: the result emitters and the `rec`-taking handlers of the fallback
-- (copies of ShippingChildFallbackA 96-325), with `StableK` instead of `StableA`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.

namespace Tools.ShippingGen4KWalkEmit
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkTranslate

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option hygiene false in
macro "karmK" : tactic => `(tactic| kwalk [makeWirePK M hA hS, emitAssignP, addInputPK M hA hS, bindSourceVariableP,
  lookupVarP, emitRegisterStmtA, emitRegisterK M hA hS, emitMemoryK M hA hS, freshNameA, emitInstanceA,
  addModuleToDesignA,
  keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))])

/-! ## The result emitters -/

section Emit
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem emitBoolResultK (rhs : Sparkle.IR.AST.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitBoolResult rhs hint named) := by
  unfold emitBoolResult
  karmK

theorem emitCompareResultK (le : SignalCompareKind) (a b hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitCompareResult le a b hint named) := by
  unfold emitCompareResult
  exact emitBoolResultK M hA hS _ _ _

theorem emitBoolLiteralK (value : Bool) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitBoolLiteral value hint named) := by
  unfold emitBoolLiteral
  exact emitBoolResultK M hA hS _ _ _

theorem emitCastResultK (rhs : Sparkle.IR.AST.Expr) (wt : Nat) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitCastResult rhs wt hint named) := by
  unfold emitCastResult
  karmK

theorem emitSliceResultK (rhs : Sparkle.IR.AST.Expr) (len : Nat) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitSliceResult rhs len hint named) := by
  unfold emitSliceResult
  karmK

theorem emitMuxResultK (c t el hint : String) (named : Bool) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (emitMuxResult c t el hint named ty) := by
  unfold emitMuxResult
  karmK

theorem emitConcatConstK (k v : Nat) :
    KeepsCP mctx mref cctx cref I (emitConcatConst k v) := by
  unfold emitConcatConst
  exact emitCastResultK M hA hS _ _ _ _

theorem translateConcatActsK (w : Nat) (hiAct loAct : CompilerM String)
    (hhi : KeepsCP mctx mref cctx cref I hiAct) (hlo : KeepsCP mctx mref cctx cref I loAct)
    (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateConcatActs w hiAct loAct hint named) := by
  unfold translateConcatActs
  refine KeepsCP.bind (makeWirePK M hA hS _ _ _) (fun _ => ?_)
  refine KeepsCP.bind hhi (fun _ => ?_)
  refine KeepsCP.bind hlo (fun _ => ?_)
  refine KeepsCP.bind (emitAssignP _ _) (fun _ => ?_)
  exact KeepsCP.pure _

end Emit

/-! ## The arms (given the recursive argument at this context) -/

section Arms
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) (rec : TranslateFn)
  (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
include M hA hS hrec

theorem translateMuxWithK (resultType : CompilerM Sparkle.IR.Type.HWType)
    (hres : KeepsCP mctx mref cctx cref I resultType) (c t el : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateMuxWith rec resultType c t el hint named) := by
  unfold translateMuxWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind hres (fun _ => ?_)
  exact emitMuxResultK M hA hS _ _ _ _ _ _

theorem translateBoolBinaryK (kind : SignalBoolBinKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateBoolBinary rec kind a b hint named) := by
  unfold translateBoolBinary
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitBoolResultK M hA hS _ _ _

theorem translateSignalCompareK (le : SignalCompareKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSignalCompare rec le a b hint named) := by
  unfold translateSignalCompare
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitCompareResultK M hA hS _ _ _ _ _

theorem translateAppCompareK (le : SignalCompareKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppCompare rec le a b hint named) := by
  unfold translateAppCompare
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitCompareResultK M hA hS _ _ _ _ _

theorem translateAppBoolBinaryK (kind : SignalBoolBinKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppBoolBinary rec kind a b hint named) := by
  unfold translateAppBoolBinary
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitBoolResultK M hA hS _ _ _

theorem translateAppBool2K (f : AppBool2) (a b : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppBool2 rec f a b hint named) := by
  unfold translateAppBool2
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (emitBoolResultK M hA hS _ _ _) (fun _ => ?_)
  exact emitBoolResultK M hA hS _ _ _

theorem translateAppBoolK (op : AppBoolOp) (a b : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppBool rec op a b hint named) := by
  unfold translateAppBool
  split
  · exact translateAppCompareK M hA hS rec hrec _ _ _ _ _
  · exact translateAppBoolBinaryK M hA hS rec hrec _ _ _ _ _
  · exact translateAppBool2K M hA hS rec hrec _ _ _ _ _

/-- **The Bool-control arm**: literals, compares, Bool binary operators, the Bool
mux, complement, applicative Bool ops — and, for any other shape, the legacy
handler handed in (`hleg`). -/
theorem translateBoolUncachedWithK (legacy : TranslateFn)
    (hleg : ∀ e hint top named, KeepsCP mctx mref cctx cref I (legacy e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateBoolUncachedWith rec legacy e hint top named) := by
  unfold translateBoolUncachedWith
  try dsimp only
  kwalk [hleg _ _ _ _, emitBoolLiteralK M hA hS _ _ _, translateSignalCompareK M hA hS rec hrec _ _ _ _ _, translateBoolBinaryK M hA hS rec hrec _ _ _ _ _, translateMuxWithK M hA hS rec hrec _ (KeepsCP.pure _) _ _ _ _ _, translateAppBoolK M hA hS rec hrec _ _ _ _ _]  -- guess: F3

theorem translateVectorMuxUncachedWithK (n : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateVectorMuxUncachedWith rec n e hint top named) := by
  unfold translateVectorMuxUncachedWith
  exact translateMuxWithK M hA hS rec hrec _ (KeepsCP.pure _) _ _ _ _ _

theorem translateSetWidthUncachedWithK (ws wt : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSetWidthUncachedWith rec ws wt e hint top named) := by
  unfold translateSetWidthUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitCastResultK M hA hS _ _ _ _

theorem translateSliceUncachedWithK (start len : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSliceUncachedWith rec start len e hint top named) := by
  unfold translateSliceUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitSliceResultK M hA hS _ _ _ _

theorem translateSliceFUncachedWithK (start len : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSliceFUncachedWith rec start len e hint top named) := by
  unfold translateSliceFUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitSliceResultK M hA hS _ _ _ _

theorem translateConcatUncachedWithK (m n : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateConcatUncachedWith rec m n e hint top named) := by
  unfold translateConcatUncachedWith translateConcatWith
  exact translateConcatActsK M hA hS _ _ _ (hrec _ _ _ _) (hrec _ _ _ _) _ _

theorem translateConcatLitUncachedWithK (hi : Bool) (k v w : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateConcatLitUncachedWith rec hi k v w e hint top named) := by
  unfold translateConcatLitUncachedWith
  refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
  · exact translateConcatActsK M hA hS _ _ _ (emitConcatConstK M hA hS _ _) (hrec _ _ _ _) _ _
  · exact translateConcatActsK M hA hS _ _ _ (hrec _ _ _ _) (emitConcatConstK M hA hS _ _) _ _

theorem translateRegisterUncachedWithK (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateRegisterUncachedWith rec w v e hint top named) := by
  unfold translateRegisterUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitRegisterK M hA hS _ _ _ _ _ _ _ _

theorem translateRegisterEnableUncachedWithK (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateRegisterEnableUncachedWith rec w v e hint top named) := by
  unfold translateRegisterEnableUncachedWith
  try dsimp only
  karmK

theorem translateLoopRegisterUncachedWithK (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateLoopRegisterUncachedWith rec w v e hint top named) := by
  unfold translateLoopRegisterUncachedWith
  try dsimp only  -- guess: F2
  karmK

theorem translateCircuitDoUncachedWithK (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateCircuitDoUncachedWith rec w v e hint top named) := by
  unfold translateCircuitDoUncachedWith
  try dsimp only  -- guess: F2
  karmK

theorem translateCircuitDo2UncachedWithK (w v0 v1 ret : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateCircuitDo2UncachedWith rec w v0 v1 ret e hint top named) := by
  unfold translateCircuitDo2UncachedWith
  try dsimp only  -- guess: F2
  karmK

theorem translateMemoryUncachedWithK (aw dw : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateMemoryUncachedWith rec aw dw e hint top named) := by
  unfold translateMemoryUncachedWith
  try dsimp only  -- guess: F3
  karmK

/-- One recursive translation per instance operand. -/
theorem instArgsK :
    ∀ (rest : List (Sparkle.IR.AST.Port × Lean.Expr)) (acc : List (String × Sparkle.IR.AST.Expr))
      (i : Nat), KeepsCP mctx mref cctx cref I (instArgs rec acc rest i)
  | [], acc, i => by unfold instArgs; exact KeepsCP.pure _
  | (p, a) :: rest, acc, i => by
    have ih := fun acc i => instArgsK rest acc i
    unfold instArgs
    refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
    exact ih _ _

end Arms

end Tools.ShippingGen4KWalkEmit
