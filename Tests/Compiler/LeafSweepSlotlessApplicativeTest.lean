import Tests.Compiler.ApplicativeSemanticsTest
import Tools.ShippingLeafSweepCommand

/-! # Leaf sweep at the design level: SlotlessApplicative (round par/b-31)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#leaf_sweep f` (`Tools/ShippingLeafSweepCommand.lean`) runs the generator of
`#machine_leaf_design` on `f` and LOGS the outcome; it is an error in no
case. Swept here — combinational applicative declarations (no register slot):

* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversed`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversedSurface`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nestedSurface`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantRight`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantLeft`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.duplicate`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.withConstant`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nested`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.complement`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.concatReverse`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.orderedLess`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.rightAssociated`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.permutedFour`

PREDICTED (by reading; `docs/parallel/B-leaf-sweep.md`): REFUSED slotless (13). NOTHING of
that is asserted here. `#leaf_sweep_summary` is an error only if a
GENERATED declaration's audit did not pass, its listing has a NOT ALLOWED
line, or a refused declaration left `machine_design_leaf0` behind.

Log: `LEAFSWEEP START f` (also on stderr) before each declaration; then
`LEAFDESIGN DATA`, `LEAFDESIGN PREMISE … ALLOWED | NOT ALLOWED` (the full
premise list by the existing classifier), `LEAFDESIGN GENERATED | REFUSED |
FAILED f: <reason>`, `LEAFDESIGN AUDIT …` (standard axioms), `GOALGAP …`,
`LEAFSWEEP RESULT f: …`; at the end `LEAFSWEEP ROW …` and `LEAFSWEEP SUMMARY`.

A GENERATED line is about ONE declaration as an entry, depth 0: data
conditions decided for it, the run / `MachineDefines f` / `ChildBnd` as
premises, `DesignSV` of the module list — not the SV string, not `#sim`.

Names added (none of them elsewhere in this file's import closure, by
reading): `f.machine_design_leaf0`, `f.machine_design_leaf0_gap`, and
`f.machine_leafKid` / `f.machine_closes` where the imports do not have them.
Do not import this file together with another generator of those names. -/

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversed

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversedSurface

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nestedSurface

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantRight

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantLeft

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.duplicate

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.withConstant

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nested

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.complement

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.concatReverse

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.orderedLess

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.rightAssociated

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.permutedFour

#leaf_sweep_summary
