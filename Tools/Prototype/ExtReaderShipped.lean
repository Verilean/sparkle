import Tools.Prototype.ExtReaderDefs

/-! # Unit EXT2: the SHIPPED operations give the shipped normaliser / wrapper (evidence: `rfl` or short proofs)

STATUS: see REPORT-EXT2.md. Kept apart from `ExtReaderDefs` because `rawNodeX shippedOps = rawNode` is not accepted by `rfl` (see the report). -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.Prototype.ReaderComposed Tools.Prototype.NormStepModel Tools.Prototype.ExtModelLetOk
open Sparkle.Compiler.MachRawSurface (projChain listElems)

theorem rawBuildX_shipped (k : Nat) (regs body : Lean.Expr) (tys : List Lean.Expr) :
    rawBuildX shippedOps k regs body tys = Sparkle.Compiler.MachRawSurface.rawNode.build k regs body tys := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨j, nm, t⟩ := a
    unfold rawBuildX
    rw [ih]
    rfl

/-- NOT PROVED (evidence only; `rfl` is not accepted: `Meta.isDefEq` cannot match the two compiled matchers on `Name`-literal patterns,
trace in the report): the node rewriter of the model reader at the shipped operations is the shipped `rawNode`. Nothing about the model
reader (`machineShapeXM`, `modelOps`) uses it; the agreement is TESTED (`Tests/Compiler/ExtReaderAgreeTest.lean`). -/
def RawNodeXShipped : Prop :=
  ∀ (pm : Name → Option Nat) (e : Lean.Expr), rawNodeX shippedOps pm e = Sparkle.Compiler.MachRawSurface.rawNode pm e

theorem normStepX_shipped (hr : RawNodeXShipped) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv)
    (e : Lean.Expr) : normStepX shippedOps node senv e = normStepP node senv e := by
  have hr' : ∀ pm e, rawNodeX shippedOps pm e = Sparkle.Compiler.MachRawSurface.rawNode pm e := hr
  cases e <;> first
    | rfl
    | (simp only [normStepX, normStepP, hr']; rfl)

theorem execNormX_shipped (hr : RawNodeXShipped) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) :
    execNormX shippedOps node senv = execNormP node senv := by
  rw [execNormX_eq_lfp, execNormP_eq_lfp]
  have : normStepX shippedOps node senv = normStepP node senv := funext (normStepX_shipped hr node senv)
  rw [this]


theorem xtabX_shipped (hr : RawNodeXShipped) (senv : StructEnv) : xtabX shippedOps senv = xtabEM senv := by
  funext c
  cases c with
  | norm e => exact congrFun (execNormX_shipped hr machNormNodeM senv) e
  | blk c => exact congrFun (execBlockX_shipped senv) c

/-- With the SHIPPED operations the reader is the NMI reader `machineShapeNM`. -/
theorem machineShapeX_shipped (hr : RawNodeXShipped) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv)
    (ai : Bool) : machineShapeX shippedOps sm ps ci senv ai = machineShapeNM sm ps ci senv ai := by
  unfold machineShapeX machineShapeNM
  rw [xtabX_shipped hr]
  rfl


end Tools.Prototype.ExtReader
