import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingFinalGoalCommand

/-! # The gap of `parent`'s closed endpoint to the final goal

`parent` (`Tests/Compiler/ShippingMachineSeqTest.lean`) has the closed depth
endpoint `parent.machine_design_svNR1_closed`
(`Tests/Compiler/ShippingCallsCloseTest.lean`). `#machine_goal_gap` reads
its actual type `∀ binders, ∃ raw D, P ∧ (A₁ → … → C)` and adds
`parent.machine_goal_gap1 : ∀ binders, kid_… → gap_… → ∃ raw D, P ∧ C`,
kernel-checked: one named `gap_…` hypothesis per antecedent the final goal
does not allow (expected from the endpoint's printed type:
`gap_shipsHierCheck`, `gap_designCheck`, `gap_outsCheck`, `gap_kidsMaskedN`;
the children's `ChildBnd ∧ MachineDefines` taken as `kid_3`). The log
(`GOALGAP`) lists them and the endpoint's own binders. Nothing is proved
about the compiler here. -/

set_option maxHeartbeats 0 in
#machine_goal_gap Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_goal_gap1
