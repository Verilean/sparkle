import Tests.Compiler.ShippingMachineRawTest
import Tools.ShippingLeafSweepCommand

/-! # Leaf sweep at the design level: Raw (round par/b-31)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#leaf_sweep f` (`Tools/ShippingLeafSweepCommand.lean`) runs the generator of
`#machine_leaf_design` on `f` and LOGS the outcome; it is an error in no
case. Swept here — `runCircuitH` counters WITHOUT an input (five), a `circuit do` pair counter, and a register machine with a tuple-typed input:

* `Sparkle.Tests.RunCircuitHTest.counterH`
* `Sparkle.Tests.RunCircuitHTest.twoCountH`
* `Sparkle.Tests.RunCircuitHTest.mixedWidthH`
* `Sparkle.Tests.RunCircuitHTest.tripleCountH`
* `Sparkle.Tests.RunCircuitHTest.fourCountH`
* `Sparkle.Tests.CircuitDoTest.pairCounterCdo`
* `Sparkle.Tests.Compiler.ShippingMachineRawTest.tupReg`

PREDICTED (by reading; `docs/parallel/B-leaf-sweep.md`): GENERATED (7). NOTHING of
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
#leaf_sweep Sparkle.Tests.RunCircuitHTest.counterH

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.RunCircuitHTest.twoCountH

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.RunCircuitHTest.mixedWidthH

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.RunCircuitHTest.tripleCountH

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.RunCircuitHTest.fourCountH

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.CircuitDoTest.pairCounterCdo

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineRawTest.tupReg

#leaf_sweep_summary
