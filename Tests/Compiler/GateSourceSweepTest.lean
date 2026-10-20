import Tests.Compiler.GateDesignSweepTest
import Tools.ShippingGateSourceCommand

/-! # Gate-route entries at the design level, the source on Signals: `pick`, `pickD`, `rcH` (round par/b-36)

WRITTEN, NOT BUILT. TARGET-ONLY until the integrator decides.

`f.gate_design0` (BUILT, 0a0a4f71; in `Tests.AllTests` through
`GateDesignSweepTest`, imported here) states the source per cycle on VALUES
(`childValue f.machineSource`, inputs `InRange`). Here each of the three
gate-route declarations gets `f.gate_pointwise` (the source's observation at
time `t` is the reflected term's value on the inputs' values at `t` — a
kernel `rfl`) and `f.gate_design0S`: the same closed-run conclusion with the
source on SIGNALS, in the form of `f.machine_design_comb0` (`SourceInputs`
of the Signals' values at every cycle; every observation of
`f.machineSource i bools bits` on the port `out`).

Names added: `f.gate_pointwise`, `f.gate_design0S`, `f.gate_design0S_gap`.

The classes below are PREDICTED (`GENERATED`), not measured; the integrator
corrects the lines from the measurement. The step most likely to fail is
`f.gate_pointwise` (the kernel must reduce the declaration applied to free
input Signals and the term's `eval` to the same expression): a FAILED row
then names it.

A GENERATED line is about ONE gate-route declaration as an entry, depth 0:
the run and `EntryDefines f f.gateValue` premises; `DesignSV` of the module
list — not the SV string, not `#sim`. -/

set_option maxHeartbeats 0 in
#gate_source_sweep Sparkle.Tests.Compiler.ShippingMachineInstTest.pick

set_option maxHeartbeats 0 in
#gate_source_sweep Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD

set_option maxHeartbeats 0 in
#gate_source_sweep Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH

#gate_source_sweep_summary

#gate_source_sweep_expect Sparkle.Tests.Compiler.ShippingMachineInstTest.pick "GENERATED"
#gate_source_sweep_expect Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD "GENERATED"
#gate_source_sweep_expect Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH "GENERATED"
