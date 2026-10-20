import Tests.Compiler.ShippingMachineCommandTest
import Tools.ShippingLeafSweepCommand
import Tools.ShippingLeafSweepExpect

/-! # Leaf sweep at the design level: Entry (round par/b-31)

WRITTEN, NOT BUILT. TARGET-ONLY — not in `Tests/AllTests.lean`.

`#leaf_sweep f` (`Tools/ShippingLeafSweepCommand.lean`) runs the generator of
`#machine_leaf_design` on `f` and LOGS the outcome; it is an error in no
case. Swept here — `circuit do` register machines of `ShippingMachineEntryTest` (three slots; a field of a structure result; the LIN checksum, generic and default domain) and the IP module `LINHW.checksumHW`:

* `Sparkle.Tests.Compiler.ShippingMachineEntryTest.mThree`
* `Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoFlag`
* `Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoCnt`
* `Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChk`
* `Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChkDefault`
* `Sparkle.IP.Bus.LINHW.checksumHW`

PREDICTED (by reading; `docs/parallel/B-leaf-sweep.md`): GENERATED (6). NOTHING of
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
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineEntryTest.mThree

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoFlag

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoCnt

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChk

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChkDefault

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.IP.Bus.LINHW.checksumHW

#leaf_sweep_summary

/-! ## The MEASURED classes, asserted (round par/b-32; WRITTEN, NOT BUILT)

The classes below are those of the integrator's build of 35208d70
(`docs/parallel/B-leaf-sweep.md`, "Integrator's build record"), not the
predictions of this file's header. `#leaf_sweep_expect` is an error when a
declaration's class changed, when a GENERATED one's audit did not pass or
its theorem is absent, or when a refusal's reason is another one. Each line
is its own command. -/

#leaf_sweep_expect Sparkle.Tests.Compiler.ShippingMachineEntryTest.mThree "GENERATED"
#leaf_sweep_expect Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoFlag "GENERATED"
#leaf_sweep_expect Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoCnt "GENERATED"
#leaf_sweep_expect Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChk "GENERATED"
#leaf_sweep_expect Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChkDefault "GENERATED"
#leaf_sweep_expect Sparkle.IP.Bus.LINHW.checksumHW "GENERATED"
