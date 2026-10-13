import Tests.Compiler.ShippingSignOpsTest
import Tools.ShippingCombLeafClosedCommand

/-! # Slotless leaves at the design level, CLOSED form, measured: SignOps (round par/b-33)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#comb_closed_sweep f` (`Tools/ShippingCombLeafClosedCommand.lean`) runs the
generator of `f.machine_design_comb0` — the design-level endpoint of a
slotless leaf with NO antecedent under the existential but `ChildBnd` — and
LOGS; it is an error in no case. Per declaration:

1. `COMBCLOSED START f` (also on stderr);
2. `COMBDESIGN0 DATA …` (the reader's data), the premise listing
   `COMBDESIGN0 PREMISE … ALLOWED | NOT ALLOWED …` by the existing classifier
   (`Tools.ShippingFinalGoalCommand.allowed`, through the register leaves'
   `checkStatementWith`), `COMBDESIGN0 GENERATED | REFUSED | FAILED f: <reason>`;
3. for a generated theorem: `COMBDESIGN0 AUDIT …` (the statement check again
   on the stored statement; standard axioms of the endpoint, the data
   theorems, the closing and the general theorems) and `GOALGAP …` (the
   parents' gap tool) — a failure of either is caught and recorded;
4. `COMBCLOSED RESULT f: …; <ms> ms`.

Swept here:

* `Sparkle.Tests.Compiler.ShippingSignOpsTest.sext`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig`
* `Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul`
* `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize`

MEASURED before this round (integrator's build of 4103e86f): the OPEN
endpoint was GENERATED for the declarations of the other four files and
REFUSED for the six of `SignOps` (a transported `machine_ships_comb`); on one
run of the real entry (S1) and (S2) held for all 32. NOTHING is asserted here
about a class or a count (the predictions are in
`docs/parallel/B-slotless-leaf-2.md`, labelled PREDICTED).
`#comb_closed_sweep_summary` is an error only if a GENERATED declaration's
audit did not pass, its listing has a NOT ALLOWED line, its theorem is
absent, or a refused declaration left the theorem behind.

A GENERATED line is about ONE declaration as an entry, depth 0, no call, no
register, one output `out`: data conditions decided for it; the run,
`MachineDefines f` and `ChildBnd` premises; `DesignSV` of the module list —
not the SV string, not `#sim`.

Names added: `f.machine_combKid`, `f.machine_combPos`,
`f.machine_design_comb0`, `f.machine_design_comb0_gap`, and `f.machine_closes`
where the imports do not have it. -/

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.sext

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrK

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.shiftSurface

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.ashrSig

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ShippingSignOpsTest.scaleMul

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.IP.YOLOv8.Primitives.Requantize.requantize

#comb_closed_sweep_summary
