import Tests.Compiler.ShippingMachineFuseTest
import Tools.ShippingLeafSweepCommand

/-! # Leaf sweep at the design level: Fuse (round par/b-31)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#leaf_sweep f` (`Tools/ShippingLeafSweepCommand.lean`) runs the generator of
`#machine_leaf_design` on `f` and LOGS the outcome; it is an error in no
case. Swept here — fused nested `Signal.loop`s (endpoints generated with `checkCloses := false`), and `withMemory`:

* `Sparkle.Tests.Compiler.ShippingMachineFuseTest.outer`
* `Sparkle.Tests.Compiler.ShippingMachineFuseTest.siblings`
* `Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory`

PREDICTED (by reading; `docs/parallel/B-leaf-sweep.md`): outer, siblings: in scope IF machine_ships_wired exists (NOT known); withMemory REFUSED (memory). NOTHING of
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
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineFuseTest.outer

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineFuseTest.siblings

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory

#leaf_sweep_summary
