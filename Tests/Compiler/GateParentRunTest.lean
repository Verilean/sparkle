import Tests.Compiler.ShippingHierarchySoundnessTest
import Tools.ShippingGateParentRun

/-! # `gate_parent_run` instantiated for `parentUse` (worker N, round 1)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateParentRunTest`;
not in `Tests.AllTests`).

`parentUse a b := childAdd a b` (a gate-route parent: one call of the
`@[hardware_module]` child `childAdd` on its binders). The pure premises of
`gate_parent_run` are discharged here per declaration (`rfl` / `decide` on the
reflected value, the S6 gate lemma `instanceN_term_gate`); the run, the
reflection `EntryDefines`, `ChildBnd`, and the two environment facts `tag` /
`hscalar` (the same two the BUILT `parentUse_instance_entry` /
`parentUse3_instance_entry` carry) stay binders. The axioms are printed. -/
namespace Sparkle.Tests.Compiler.GateParentRunTest
open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Tools.ShippingInstanceEntrySoundness (instEN instanceN_term_gate)
open Tools.ShippingGateParentRun
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMixedSourceBridge (inputExpr instantiated_input)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInv (ChildBnd RealChild Res)

/-- `parentUse`'s value peels to the n-ary canonical call (the term of the
built `parentUse_peel`, `instEN` unfolded). -/
theorem parentUse_peelN : mixedGatePeel parentUseValue = some (parentUseBinders,
    instEN ``childAdd [] (inputExpr parentUseBinders.length 0)
      ([1, 2].map (inputExpr parentUseBinders.length))) := rfl

set_option maxRecDepth 4096 in
theorem parentUse_pure : (``childAdd == ``Sparkle.Core.Signal.Signal.pure) = false := by
  first | rfl | decide | decide +kernel

set_option maxRecDepth 4096 in
theorem parentUse_binOp : signalBinOpOf ``childAdd = none := by
  first
    | rfl
    | decide
    | decide +kernel
    | exact Option.isNone_iff_eq_none.mp (by first | decide | decide +kernel)

set_option maxRecDepth 4096 in
/-- The instantiated call is not one of the fallback's certified shapes. -/
theorem parentUse_kind (ids : List FVarId) (hlen : ids.length = parentUseBinders.length) :
    fallbackKind (instEN ``childAdd []
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 (inputExpr parentUseBinders.length 0))
      (([1, 2].map fun q => ids[q]!).map Lean.Expr.fvar)) = .other := by
  rw [instantiated_input (j := 0) hlen (by decide)]
  first | rfl | decide | decide +kernel

/-- **`gate_parent_run` on `parentUse`.** -/
theorem parentUse_gate_parent_run {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentUse) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref ``parentUse parentUseValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childAdd = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentUseValue →
      mixedGateResultScalar dv.type = true)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (y : Res) (ids : List FVarId)
      (cache : IO.Ref (Lean.ExprStructMap String)),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      b.name = M.name ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → design.modules = D.modules) ∧
      RealChild mref cref ``childAdd y ∧ ids.Nodup ∧ ids.length = parentUseBinders.length ∧
      InstanceNShape ``parentUse parentUseBinders ids cache ([1, 2].map fun q => ids[q]!) y M D :=
  gate_parent_run (bs := parentUseBinders) (mn := ``childAdd) (lvls := [])
    (dE := inputExpr parentUseBinders.length 0) (poss := [1, 2])
    hr entry tag hscalar
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    (fun dv hv hs isInst hI =>
      instanceN_term_gate (d := dv) (by rw [hv]; exact parentUse_peelN) hI hs ⟨_, _, rfl⟩
        (fun q hq => by
          simp at hq
          rcases hq with rfl | rfl <;> exact ⟨_, _, rfl⟩))
    (fun q hq => by
      simp at hq
      rcases hq with rfl | rfl <;> decide)
    parentUse_pure parentUse_binOp parentUse_kind bnd

end Sparkle.Tests.Compiler.GateParentRunTest

#print axioms Sparkle.Tests.Compiler.GateParentRunTest.parentUse_gate_parent_run
#print axioms Tools.ShippingGateParentRun.gate_parent_run
