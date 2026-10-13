import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingCombLeafClosedCommand
import Tools.ShippingCombLeafClosedExpect

/-! # Slotless leaves at the design level, CLOSED form: `pickByteH` (round par/b-35)

WRITTEN, NOT BUILT. TARGET-ONLY until the integrator decides.

MEASURED by the census of 20ab638e: `pickByteH`
(`Tests/Compiler/ShippingMachineLinkedTest.lean` 21: a `@[hardware_module]`
byte selector with shared `let`s, the slotless machine CHILD of `callerL` /
`callerLN`) is `OPEN slotless-leaf` — it has `machine_ships_comb` and was
simply not in a sweep file. Here it is swept as an ENTRY.

The import is `ShippingCallsCloseTest` (which imports
`ShippingMachineLinkedTest`): that file closes `callerL` over `pickByteH`,
so `pickByteH.machine_closes` is already in the environment and is not
generated a second time here (no name clash in `Tests.AllTests`). Names
added: `pickByteH.machine_combKid`, `.machine_combPos`,
`.machine_design_comb0`, `.machine_design_comb0_gap`.

The class below is PREDICTED (`GENERATED`: no call, no register, one
`BitVec 8` result, the shape of `pickByte`, which was GENERATED [MEASURED,
7d8d56b1]); the integrator corrects it from the measurement.

A GENERATED line is about ONE declaration as an entry, depth 0, no call, no
register, one output `out`: data conditions decided for it; the run,
`MachineDefines f` and `ChildBnd` premises; `DesignSV` of the module list —
not the SV string, not `#sim`. It says nothing about `pickByteH` as a CHILD
of `callerL`. -/

set_option maxHeartbeats 0 in
#comb_closed_sweep Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH

#comb_closed_sweep_summary

-- PREDICTED class (not measured before this round)
#comb_closed_sweep_expect Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH "GENERATED"
