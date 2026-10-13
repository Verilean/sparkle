import Tests.Compiler.ShippingMachineRawTest
import Tools.ShippingLeafSweepCommand

/-! # Leaf sweep at the design level: SlotlessRaw (round par/b-31)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#leaf_sweep f` (`Tools/ShippingLeafSweepCommand.lean`) runs the generator of
`#machine_leaf_design` on `f` and LOGS the outcome; it is an error in no
case. Swept here — combinational machine-route declarations (no register slot):

* `Sparkle.Tests.Compiler.ShippingMachineRawTest.negSig`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.negLift`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.addThree`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.useHalf`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.triBundle`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.tupFst`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.tupMapFst`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.tupSum`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.tupHwLet3`

PREDICTED (by reading; `docs/parallel/B-leaf-sweep.md`): REFUSED slotless (9). NOTHING of
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
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.negSig

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.negLift

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.addThree

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.useHalf

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.triBundle

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.tupFst

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.tupMapFst

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.tupSum

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.tupHwLet3

#leaf_sweep_summary
