import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingFinalGoalCommand
import Tools.ShippingShipsNoOutsCommand

/-! # The gap of `parent`'s closed endpoint to the final goal

`parent` (`Tests/Compiler/ShippingMachineSeqTest.lean`) has the closed depth
endpoint `parent.machine_design_svNR1_closed`
(`Tests/Compiler/ShippingCallsCloseTest.lean`). `#machine_goal_gap` reads
its actual type `∀ binders, ∃ raw D, P ∧ (A₁ → … → C)` and adds
`parent.machine_goal_gap1 : ∀ binders, kid_… → gap_… → ∃ raw D, P ∧ C`,
kernel-checked: one named `gap_…` hypothesis per antecedent the final goal
does not allow (`gap_shipsHierCheck`, `gap_designCheck`, `gap_outsCheck`,
`gap_kidsMaskedN`; the children's `ChildBnd ∧ MachineDefines` taken as
`kid_3`). The log (`GOALGAP`) lists them and the endpoint's own binders.

## One check removed from a real run (round 13)

`parent_outs` proves the output check of `parent`'s CORE run's design from
the run (`Tools.ShippingChecksCore.core_outsCheck_all`; the child `cnt` is
a leaf with a register: `leaf_real_kidA`, `leaf_real_kidR`). With it,
`#machine_no_outs` adds `parent.machine_design_noOutsNR1` and its `_closed`
form — the statement of `parent.machine_design_svNR1(_closed)` WITHOUT the
`outsCheck` antecedent — through the head that exposes the core run
(`Tools.ShippingShipsNoOuts.machine_design_noOuts`). `#machine_goal_gap_of`
on the closed form must then log THREE `NOT ALLOWED` antecedents. -/

set_option maxHeartbeats 0 in
#machine_goal_gap Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_goal_gap1

namespace Tests.Compiler.FinalGoalTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
/-- **`outsCheck` of `parent`'s core run's design**, at depth 1, from the
run: the hypotheses are the core run, the post-processing fact, `parent`'s
reflection and closing, the optimizer gate `hierBinds b` (which
`shipsHierCheck` gives), and the endpoint's own boundary (the child
boundary of the start world and `cnt`'s reflection). -/
theorem parent_outs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``parent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``parent
      parent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``parent
      parent.machineData.shape)
    (hb : Sparkle.IR.RefineCheck.hierBinds b = true)
    (hBnd : Tools.ShippingChildInv.ChildBnd mref cref w ∧
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingChecksCore.core_outsCheck_all (nDecl := 1) parent.machineData parent.machine_ok
    parent.machine_body (by decide) (by decide) (by decide)
    (fun h => absurd (congrArg List.length h) (by decide)) (by decide) (by decide)
    (by
      intro k hk y hy
      -- two entries (the fields `n` and `hit` of the ONE call of `cnt`)
      have hk' : k < 2 := hk
      have hA := fun (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
          (hy : Tools.ShippingChildInv.RealChild mref cref ``cnt y) =>
        Tools.ShippingChecksRun2.leaf_real_kidA cnt.machineData cnt.machine_ok
          cnt.machine_body rfl (fun h => absurd (congrArg List.length h) (by decide))
          (by decide) (by decide) hBnd.2 (fun mc cc => cnt.machine_closes mc _ cc _) hy
      cases k with
      | zero => exact hA y hy
      | succ k =>
        cases k with
        | zero => exact hA y hy
        | succ k => exact absurd hk' (by omega))
    (by
      intro k hk y hy
      have hk' : k < 2 := hk
      have hR := fun (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
          (hy : Tools.ShippingChildInv.RealChild mref cref ``cnt y) =>
        Tools.ShippingChecksCore.leaf_real_kidR cnt.machineData cnt.machine_ok
          cnt.machine_body rfl (by decide) hBnd.2 (fun mc cc => cnt.machine_closes mc _ cc _) hy
      cases k with
      | zero => exact hR y hy
      | succ k =>
        cases k with
        | zero => exact hR y hy
        | succ k => exact absurd hk' (by omega))
    hBnd.1 hcore hpost entry closes hb 1

end Tests.Compiler.FinalGoalTest

set_option maxHeartbeats 0 in
#machine_no_outs Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1 using
  Tests.Compiler.FinalGoalTest.parent_outs

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noOutsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noOutsNR1_closed
