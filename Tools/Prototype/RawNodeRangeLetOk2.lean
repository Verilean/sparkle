import Tools.Prototype.RawNodeRangeLetOk

/-! # Unit LC18b: the `LiftRange` premise of `machineShapeN_typed_all_rawNode` was a duplicate

BUILT (unit LC18b): a1 exit 1 (my meta-check errors), a2 exit 0.  No sorry / axiom / native_decide.

`LiftLooseRange` (`∀ e s d, LetOk 0 e → LetOk 0 (e.liftLooseBVars s d)`) implies `LiftRange`
(`∀ e, LetOk 0 e → LetOk 0 (e.liftLooseBVars 0 1) ∧ LetOk 0 (e.liftLooseBVars 1 1)`): the instances `s d = 0 1` and `1 1`.
PROVED: `liftRange_of_loose`.  PROVED: the corollary `machineShapeN_typed_all_rawNode'` has the same conclusion as
`machineShapeN_typed_all_rawNode` and NO `LiftRange` binder.  `LiftLooseRange` itself remains a PREMISE (not proved).
The old theorems are unchanged. -/
namespace Tools.Prototype.RawNodeRangeLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.StartDomOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge

theorem liftRange_of_loose (hll : LiftLooseRange) : LiftRange :=
  fun e he => ⟨hll e 0 1 he, hll e 1 1 he⟩

/-- `machineShapeN_typed_all_rawNode` without the duplicate `hlift : LiftRange` (derived from `hll`). -/
theorem machineShapeN_typed_all_rawNode' {senv : StructEnv}
    (hroot : RootFloatRange) (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    (hz : ZeroLitAgrees) (hll : LiftLooseRange) (hlo : LowerLooseRange) (hbeta : BetaRange)
    (hnode : NormNodeRange senv) (hE : EqvLetOk0)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) :=
  machineShapeN_typed_all_rawNode hroot (liftRange_of_loose hll) hinst1 hsig hz hll hlo hbeta hnode hE hpe h

#print axioms liftRange_of_loose
#print axioms machineShapeN_typed_all_rawNode'

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_typed_all_rawNode'
  ["RootFloatRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "LiftLooseRange", "LowerLooseRange",
    "BetaRange", "NormNodeRange", "EqvLetOk0", "Eq", "Eq"])

/- THROWING: no `LiftRange` constant in the new type; the conclusion is `isDefEq` to the old one with the shared
binders as the same fvars (the old `hlift` binder is a fresh mvar; it is a non-dependent Prop). -/
run_meta (do
  let newI ← getConstInfo ``machineShapeN_typed_all_rawNode'
  let oldI ← getConstInfo ``machineShapeN_typed_all_rawNode
  if newI.type.getUsedConstants.contains ``LiftRange then throwError "LiftRange occurs in the new type"
  Meta.forallTelescope newI.type fun xs nb => do
    let mut oty := oldI.type
    let mut i := 0
    let mut skipped := false
    for _ in [0:xs.size + 1] do
      match oty with
      | .forallE n d b bi =>
        if n == `hlift then
          if skipped then throwError "two hlift binders"
          skipped := true
          oty := b.instantiate1 (← Meta.mkFreshExprMVar d)
        else
          unless i < xs.size do throwError "old type has more binders than new"
          unless (← xs[i]!.fvarId!.getUserName) == n do throwError "binder name mismatch at {i}: {n}"
          oty := b.instantiate1 xs[i]!
          i := i + 1
      | _ => break
    unless skipped && i == xs.size do throwError "binder bookkeeping failed ({skipped}, {i}, {xs.size})"
    unless (← Meta.isDefEq oty nb) do throwError "conclusions are not defeq"
    logInfo m!"LC18b check: conclusions defeq, {xs.size} shared binders, no LiftRange constant")

end Tools.Prototype.RawNodeRangeLetOk
