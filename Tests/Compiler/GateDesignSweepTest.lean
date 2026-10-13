import Tests.Compiler.ShippingMachineInstTest
import Tests.Compiler.ShippingMachineDepthHTest
import Tools.ShippingGateDesignCommand

/-! # Gate-route declarations as entries at the design level: `pick`, `pickD`, `rcH` (round par/b-35)

WRITTEN, NOT BUILT. TARGET-ONLY until the integrator decides.

MEASURED by the census of 20ab638e: `pick`, `pickD`
(`Tests/Compiler/ShippingMachineInstTest.lean` 29, 78) and `rcH`
(`Tests/Compiler/ShippingMachineDepthHTest.lean` 20) are the three
declarations with `gateValue` — instance-free combinational declarations the
certified unified gate compiles, used so far only as CHILDREN (`#gate_child`,
`GateRun`). Here each is swept as an ENTRY: `#gate_design_sweep f` runs
`#gate_design0`'s generator (`f.gate_design0`), its audit and the gap tool.

The gate data (`f.gateValue`, `f.gateBinders`, `f.gate_old`, `f.gate_peel`,
`f.gate_wf`, `f.machineSource`, `f.gate_child`) is in the environment from
the imports: `#gate_child pick` / `pickD` in `ShippingMachineInstTest`,
`#machine_composed midH` (which generates `rcH`'s) in
`ShippingMachineDepthHTest`. Names added here: `f.gate_design0`,
`f.gate_design0_gap`.

No class is asserted (nothing is measured yet). PREDICTED, in
`docs/parallel/B-gate-entry.md`: GENERATED for the three. After the
measurement the integrator can add
`#gate_design_sweep_expect f "GENERATED"` lines.

A GENERATED line is about ONE gate-route declaration as an entry, depth 0:
the run and `EntryDefines f f.gateValue` premises; the source per cycle on
values (`childValue f.machineSource`), inputs `InRange`; `DesignSV` of the
module list — not the SV string, not `#sim`. It says nothing about the
declaration as a CHILD of `caller` / `midH`. -/

set_option maxHeartbeats 0 in
#gate_design_sweep Sparkle.Tests.Compiler.ShippingMachineInstTest.pick

set_option maxHeartbeats 0 in
#gate_design_sweep Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD

set_option maxHeartbeats 0 in
#gate_design_sweep Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH

#gate_design_sweep_summary
