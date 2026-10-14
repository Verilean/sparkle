import Tests.Compiler.GateParentRunTest
import Tools.ShippingGateParentRunG

/-! # `gate_parent_runG` instantiated for `parentUse` (worker N, round 2)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateParentRunGTest`).

The binders: the run, `GateDefines` (the ONE reflection premise; NOT ALLOWED
until the classifier admits it), `ChildBnd`. Every other premise is decided
here on the reflected body. The axioms are printed. -/
namespace Sparkle.Tests.Compiler.GateParentRunGTest
open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateParentRunTest
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingChildInv (ChildBnd RealChild Res)

/-- `parentUse`'s body as the gate reads it. -/
abbrev parentUseBody : Lean.Expr :=
  instEN ``childAdd [] (inputExpr parentUseBinders.length 0)
    ([1, 2].map (inputExpr parentUseBinders.length))

set_option maxRecDepth 8192 in
/-- Only an instance disjunct accepts the body: with the body not designated,
the gate's condition is false. -/
theorem parentUse_sel : MixedGateSel (parentUseBinders.map (·.2)).toArray parentUseBody := by
  intro isInst sc hI
  unfold mixedGateCond unifiedInstanceRoot hierInstRoot
  rw [hI]
  rfl

/-- **`gate_parent_runG` on `parentUse`.** -/
theorem parentUse_gate_parent_runG {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentUse) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentUse parentUseBinders parentUseBody)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (y : Res) (ids : List FVarId)
      (cache : IO.Ref (Lean.ExprStructMap String)),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      b.name = M.name ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → design.modules = D.modules) ∧
      RealChild mref cref ``childAdd y ∧ ids.Nodup ∧ ids.length = parentUseBinders.length ∧
      InstanceNShape ``parentUse parentUseBinders ids cache ([1, 2].map fun q => ids[q]!) y M D :=
  gate_parent_runG (bs := parentUseBinders) (mn := ``childAdd) (lvls := [])
    (dE := inputExpr parentUseBinders.length 0) (poss := [1, 2])
    hr gdef parentUse_sel (by simp)
    (fun q hq => by
      simp at hq
      rcases hq with rfl | rfl <;> decide)
    parentUse_pure parentUse_binOp parentUse_kind bnd

end Sparkle.Tests.Compiler.GateParentRunGTest

#print axioms Sparkle.Tests.Compiler.GateParentRunGTest.parentUse_gate_parent_runG
#print axioms Tools.ShippingGateParentRun.gate_parent_runG
