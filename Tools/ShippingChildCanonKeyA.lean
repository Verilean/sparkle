import Tools.ShippingChildLoopsCP
import Tools.ShippingChildFallbackA
-- BUILT (unit A, round 2): a1-a9 exit 1 (print, names, statement ascription, timeouts on unification, `swap` absent), a10 exit 0. No `sorry`, no `axiom`, no `native_decide`, no new law / boundary
-- field. Law witness: `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only
-- (the two ref reads `sparkleWireCanon.get` / `sparkleLoopWireCache.get` are `FramedA.sideGetIO`).
/-! # `CanonKeyA`: the multi-output call key keeps a stable `I`

`canonHardwareKey a = toString (← canonHardwareExpr a).hash`, with
`canonHardwareExpr = fuelFixM canonHardwareExprStep helperFuelLimit`. The step has NO
`whnf`/`instantiateMVars`: it reads two side refs (`FramedA.sideGetIO`), the compiler's variable
map (`lookupVarP`), the local context (`findDecl?` is a pure read: `Keeps.of_ok`), loops over
`List`/`Array`/`Range` (`Tools/ShippingChildLoopsCP.lean`) and the recursive call on loop
sub-expressions (the fuel induction, `KeepsCP.fuelFixM`). PROVED with no premise:
`canonKeyA : CanonKeyA O I` (given `StableA O.quiet I`). -/
namespace Tools.ShippingChildCanonKeyA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildLoopsCP
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFresh

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

-- The tail (`__do_jp`): the wire substitution over the free variables (a `forIn` over the
-- `fvarIds` with `lookupVar`, then a pure `replace`).
set_option hygiene false in
macro "ctail" : tactic => `(tactic|
  (refine KeepsCP.bind (KeepsCP.forIn_array _ (fun fv repl => ?_) _ _) (fun _ => KeepsCP.pure _)
   refine KeepsCP.bind (lookupVarP fv) (fun _ => KeepsCP.pure _)))

section Step
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- **One step of `canonHardwareExpr`**, given the recursive call. -/
theorem canonHardwareExprStepA (rec : Lean.Expr → CompilerM Lean.Expr)
    (hrec : ∀ a, KeepsCP mctx mref cctx cref I (rec a)) (value : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (canonHardwareExprStep rec value) := by
  unfold canonHardwareExprStep
  refine KeepsCP.bind (KeepsCP.lift (keepsA_framed O hA hS (FramedA.sideGetIO SideRef.wireCanon)))
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
    ctail
    refine KeepsCP.bind (KeepsCP.lift (keepsA_framed O hA hS
      (FramedA.sideGetIO SideRef.loopWire))) (fun cache => ?_)
    refine KeepsCP.bind (KeepsCP.forIn_array _ (fun l loopRepl => ?_) _ _) (fun lr => ?_)
    · refine KeepsCP.bind (hrec l) (fun k => ?_)
      try dsimp only
      split <;> exact KeepsCP.pure _
    · refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
      all_goals ctail

theorem canonHardwareExprA (value : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (canonHardwareExpr value) := by
  unfold canonHardwareExpr
  exact KeepsCP.fuelFixM canonHardwareExprStep
    (fun rec hrec a => canonHardwareExprStepA O hA hS rec hrec a) helperFuelLimit value

theorem canonHardwareKeyA (value : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (canonHardwareKey value) := by
  unfold canonHardwareKey
  exact KeepsCP.bind (canonHardwareExprA O hA hS value) (fun _ => KeepsCP.pure _)

end Step

/-- **`CanonKeyA`, no premise**: the multi-output call key keeps every stable `I`. -/
theorem canonKeyA (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) : CanonKeyA O I :=
  fun _ _ hA a => canonHardwareKeyA O hA hS a

end Tools.ShippingChildCanonKeyA
