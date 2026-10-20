# Verification record: the five memory-only parents closed (round par/a-19)

Tree: poc 4bd77170 + the files of par/a-19 (0ebd1020, worker files unchanged) + one `lean_lib` + five
imports in `Tests/AllTests.lean`. All targets built at the first attempt.

## Established

For each of `memCounter`, `syncNarrow`, `memWide`, `twoMems` (the same memory twice, different argument
lets), `mixedMems` (a combo and a sync memory of the same widths): `f.machine_design_noPortsR0_closed` —
the binder `MachineClosesAt f` of the At-form open endpoint is gone and NOTHING is added (`f_closes` has
no premise: a memory child has no reflection). Premises: the run, `MachineDefines f`, and under the
existentials `ChildBnd`; all ALLOWED; goal-gap theorem with no gap hypothesis; no checker constant;
standard axioms.

What it is relative to: a NEW statement — these parents have no base closed endpoint. Against
`f.machine_design_sv0`: the four checks (`shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0`) are
absent, the boundary `True` is `ChildBnd`, and the all-worlds `MachineCloses f` premise (undischargeable,
see verification-b15.md) has nothing in its place.

General theorem: `Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly` — one application of
`machineClosesAt_of_kidsDM` with the child interface discharged by `memKid_iface`; hypotheses are decided
reader data (`hsep` / `hparent` on the memory module names are decided per declaration, not proved in
general). `hfieldsNd` asks distinctness only when callee, argument lets and field all agree: true for
`twoMems` (argument lets differ); it would be false for one memory read twice on the same four lets, and
each test's first command throws on such data.

Scope: one declaration each, depth 0, register parent (slots = 2), decided data conditions, runtime
boundary, `DesignSV` of the module list, not the SV string, not `#sim`. Memory children at depth ≥ 1 are
not covered (needs a statement change of `designCheck`).

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-063815-a19-tests: lake build Tools.ShippingMemOnlyCloses Tests.Compiler.NoPortsMemOnlyClosedLib Tests.Compiler.NoPortsMemOnlyClosedMemCounterTest Tests.Compiler.NoPortsMemOnlyClosedSyncNarrowTest Tests.Compiler.NoPorts
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=986415104
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (599 jobs).
```
```
20261013-063901-a19-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=463310848
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1227 jobs).
```

## Log excerpts (a19-tests)

```
mWideTest.lean:156:0: MEMONLY CLOSED AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide: Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0_closed_gap on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly (a corollary of Tools.ShippingMemCloses.machineClosesAt_of_kidsDM with the child interface discharged by memKid_iface) an
xedMemsTest.lean:228:0: MEMONLY CLOSED AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed_gap on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly (a corollary of Tools.ShippingMemCloses.machineClosesAt_of_kidsDM with the child interface dischar
oMemsTest.lean:156:0: MEMONLY CLOSED AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed_gap on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly (a corollary of Tools.ShippingMemCloses.machineClosesAt_of_kidsDM with the child interface discharged by m
mCounterTest.lean:156:0: MEMONLY CLOSED AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0_closed_gap on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly (a corollary of Tools.ShippingMemCloses.machineClosesAt_of_kidsDM with the child interface dis
ncNarrowTest.lean:156:0: MEMONLY CLOSED AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPortsR0_closed_gap on standard axioms, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly (a corollary of Tools.ShippingMemCloses.machineClosesAt_of_kidsDM with the child interface discharged by memK
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
```
