import Tests.Compiler.ShippingMachineCombTest
import Tests.Compiler.ShippingSignOpsTest
import Tools.ShippingLeafSweepCommand

/-! # Leaf sweep at the design level: SlotlessMisc (round par/b-31)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#leaf_sweep f` (`Tools/ShippingLeafSweepCommand.lean`) runs the generator of
`#machine_leaf_design` on `f` and LOGS the outcome; it is an error in no
case. Swept here — combinational declarations of `ShippingMachineCombTest` and `ShippingSignOpsTest` (no register slot):

* `Sparkle.Tests.Compiler.ShippingMachineCombTest.pickByte`
* `Sparkle.IP.Net.IPv4.ipv4HeaderByte`
* `Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig`
* `Sparkle.IP.Net.HTTP.httpGetByte`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.sext`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul`
* `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize`

PREDICTED (by reading; `docs/parallel/B-leaf-sweep.md`): REFUSED slotless (10). NOTHING of
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
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineCombTest.pickByte

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.IP.Net.IPv4.ipv4HeaderByte

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.IP.Net.HTTP.httpGetByte

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.sext

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.IP.YOLOv8.Primitives.Requantize.requantize

#leaf_sweep_summary
