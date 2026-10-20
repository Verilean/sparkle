import Tests.Compiler.ApplicativeSemanticsTest
import Tools.ShippingCombLeafClosedCommand
import Tools.ShippingCombLeafClosedExpect

/-! # Slotless leaves at the design level, CLOSED form, measured: ApplicativeA (round par/b-33)

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

* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversed`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversedSurface`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nestedSurface`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantRight`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantLeft`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.duplicate`
* `Sparkle.Tests.Compiler.ApplicativeSemanticsTest.withConstant`

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
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversed

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversedSurface

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nestedSurface

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantRight

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantLeft

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.duplicate

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ApplicativeSemanticsTest.withConstant

#comb_closed_sweep_summary

/-! ## The MEASURED classes, asserted (round par/b-34; WRITTEN, NOT BUILT)

MEASURED by the integrator's build of 7d8d56b1: `f.machine_design_comb0`
GENERATED for all 32 slotless leaves (3 premise lines, 0 NOT ALLOWED, audit
OK). `#comb_closed_sweep_expect` is an error when a declaration's class
changed, when its audit did not pass, or when its theorem is absent. Each
line is its own command. -/

#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversed "GENERATED"
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.reversedSurface "GENERATED"
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.nestedSurface "GENERATED"
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantRight "GENERATED"
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.constantLeft "GENERATED"
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.duplicate "GENERATED"
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ApplicativeSemanticsTest.withConstant "GENERATED"
