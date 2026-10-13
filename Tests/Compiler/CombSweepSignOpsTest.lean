import Tests.Compiler.ShippingSignOpsTest
import Tools.ShippingCombLeafCommand

/-! # Slotless leaves at the design level, measured: SignOps (round par/b-32)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

The declarations below were REFUSED "slotless" by `#machine_leaf_design`
(MEASURED: `docs/parallel/B-leaf-sweep.md`, the integrator's build record of
35208d70). `#comb_sweep f` (`Tools/ShippingCombLeafCommand.lean`) is an
error in no case. Per declaration it

1. logs `COMBSWEEP START f` (also on stderr);
2. runs the REAL entry on `f` and logs `COMBSWEEP MODULE f: …` — on the
   module `b` it returned: (S1) `simpleBody b`, (S2) `checkedOptimize b == b`
   / `printOk (checkedOptimize b)`, `printOk b`, `PrintCheck.moduleCheck b`,
   whether `b` has a slice / concatenation / NOT / comparison assignment, the
   statement count, the port names. ONE run, evaluated — not a proof;
3. runs the generator of the OPEN endpoint `f.machine_design_comb0_open` and
   logs `COMBDESIGN DATA`, the premise lines (`ALLOWED` / `NOT ALLOWED
   (OPEN)`), `COMBDESIGN GENERATED | REFUSED | FAILED f: <reason>`;
4. logs `COMBSWEEP RESULT f: …`.

Swept here — sign extension, arithmetic shifts, a widening multiplication, the requantize pipeline:

* `Sparkle.Tests.Compiler.ShippingSignOpsTest.sext`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul`
* `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize`

NOTHING is asserted about a class or a count (the predictions are in
`docs/parallel/B-slotless-leaf.md`, labelled PREDICTED).
`#comb_sweep_summary` is an error only on an inconsistency of what this file
measured.

A `GENERATED` line is NOT a design-level endpoint of the final goal's form:
`f.machine_design_comb0_open` has two NOT ALLOWED antecedents, (S1)
`simpleBody b = true` and (S2) `checkedOptimize b = b ∨ printOk
(checkedOptimize b) = true`. It says: for ONE declaration as an entry, depth
0, no call, no register, one output `out`, with data conditions decided for
it, from the run, `MachineDefines f`, `ChildBnd` AND (S1), (S2): `DesignSV`
of the module list (not the SV string, not `#sim`) shows the source.

Names added: `f.machine_combKid`, `f.machine_design_comb0_open`, and
`f.machine_closes` where the imports do not have it. -/

set_option maxHeartbeats 0 in
#comb_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.sext

set_option maxHeartbeats 0 in
#comb_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK

set_option maxHeartbeats 0 in
#comb_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface

set_option maxHeartbeats 0 in
#comb_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig

set_option maxHeartbeats 0 in
#comb_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul

set_option maxHeartbeats 0 in
#comb_sweep Sparkle.IP.YOLOv8.Primitives.Requantize.requantize

#comb_sweep_summary
