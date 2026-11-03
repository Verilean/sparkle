import Tools.ShippingGen4KWalkInst
import Tools.ShippingChildLoopsCP
-- BUILT: kjob lake build Tools.ShippingGen4KWalkCanon exit 0 (rt167, source as of de85ce20); axioms standard only. Clean build is the coder's. S3 (part 4) of scripts/gen4/KWALK_PLAN.md: `canonHardwareKey` (the multi-output call key) for `StableK` (copy of ShippingChildCanonKeyA, the two side-ref reads are `FramedNM.sideGetIO`).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkCanon
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildLoopsCP
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option hygiene false in
macro "ctailK" : tactic => `(tactic|
  (refine KeepsCP.bind (KeepsCP.forIn_array _ (fun fv repl => ?_) _ _) (fun _ => KeepsCP.pure _)
   refine KeepsCP.bind (lookupVarP fv) (fun _ => KeepsCP.pure _)))

section Step
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

/-- **One step of `canonHardwareExpr`**, given the recursive call. -/
theorem canonHardwareExprStepK (rec : Lean.Expr → CompilerM Lean.Expr)
    (hrec : ∀ a, KeepsCP mctx mref cctx cref I (rec a)) (value : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (canonHardwareExprStep rec value) := by
  unfold canonHardwareExprStep
  refine KeepsCP.bind (KeepsCP.lift (keepsK_framedNM M hA hS (FramedNM.sideGetIO SideRefNM.wireCanon)))
    (fun canon => ?_)
  dsimp only
  refine KeepsCP.bind (KeepsCP.forIn_range _ (fun _ v => ?_) _ _) (fun v1 => ?_)
  · try dsimp only
    refine KeepsCP.bind (KeepsCP.forIn_array _ (fun fv repl => ?_) _ _) (fun repl => ?_)
    · try dsimp only
      refine KeepsCP.bind (lookupVarP fv) (fun x => ?_)
      refine KeepsCP.ite (fun _ => KeepsCP.pure _) (fun _ => ?_)
      refine KeepsCP.bind (KeepsCP.lift (Keeps.of_ok fun w => ⟨_, rfl⟩)) (fun d => ?_)
      cases d with
      | none => exact KeepsCP.pure _
      | some decl =>
        dsimp only
        split <;> exact KeepsCP.pure _
    · exact KeepsCP.ite (fun _ => KeepsCP.pure _) (fun _ => KeepsCP.pure _)
  · try dsimp only
    refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
    rotate_left
    ctailK
    refine KeepsCP.bind (KeepsCP.lift (keepsK_framedNM M hA hS
      (FramedNM.sideGetIO SideRefNM.loopWire))) (fun cache => ?_)
    refine KeepsCP.bind (KeepsCP.forIn_array _ (fun l loopRepl => ?_) _ _) (fun lr => ?_)
    · refine KeepsCP.bind (hrec l) (fun k => ?_)
      try dsimp only
      split <;> exact KeepsCP.pure _
    · refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
      all_goals ctailK

theorem canonHardwareExprK (value : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (canonHardwareExpr value) := by
  unfold canonHardwareExpr
  exact KeepsCP.fuelFixM canonHardwareExprStep
    (fun rec hrec a => canonHardwareExprStepK M hA hS rec hrec a) helperFuelLimit value

theorem canonHardwareKeyK (value : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (canonHardwareKey value) := by
  unfold canonHardwareKey
  exact KeepsCP.bind (canonHardwareExprK M hA hS value) (fun _ => KeepsCP.pure _)

end Step

#print axioms canonHardwareKeyK

end Tools.ShippingGen4KWalkCanon
