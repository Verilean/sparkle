# Verification record: memory-only parents `memCounter`, `syncNarrow`, `twoMems` (round par/b-14)

Tree: poc 9f279734 + the files of par/b-14 (b3ed198e, worker files unchanged) + one `lean_lib` + three imports
in `Tests/AllTests.lean`. All five targets built at the first attempt.

## What changed in the statements — an EXCHANGE, not a pure reduction

For each of `memCounter`, `syncNarrow` (first use of the sync read kind), `twoMems` (two memory entries),
against `f.machine_design_sv0`, the new `f.machine_design_noPorts0` (depth 0, OPEN form):
- absent: `shipsHierCheck`, `kidsMem`, `designCheck … 0`, `outsCheck … 0`;
- ADDED: the antecedent `ChildBnd mref cref w` where the old endpoint had `True` (the built `kidsM_*` /
  `core_*M` theorems start from `machine_run_of_core … hB`);
- unchanged: the binder `MachineCloses f` — the ALL-WORLDS closing, not `MachineClosesAt` — plus the run and
  `MachineDefines f`.

## Why these are NOT counted as check-free endpoints

`MachineCloses` over all worlds was found over-stated for shapes with calls earlier in this project (the At
form replaced it elsewhere), and whether it can hold of a memory-only parent was NOT read. If it cannot,
both the old `…sv0` and the new `…noPorts0` are vacuous. Until that is settled, nothing here is reported as
a removed premise of a meaningful endpoint.

Probe only (`NoPortsMemOnlyAtProbe`, target-built, logs): the At-form endpoint
`memCounter.machine_design_noPortsR0` was GENERATED with premises run, `MachineDefines memCounter`,
`MachineClosesAt memCounter` (NOT ALLOWED), `ChildBnd` — the form that a closing theorem for memory
children would discharge. `mixedMems`, `memWide`: not written.

Measured (earlier probe): all five memory-only parents have slots = 2, loops = 1 (a register exists);
`#machine_design_svR0 memCounter` is REFUSED ("no sequential child").

New general statements (Tools/ShippingMemOnly.lean, no scripted copy): `kidsMem_of`, `core_kidsMemM`,
`MemOnlyData`, `memOnly_kids`, `memOnly_runFacts/_outsCheck/_kidsMem/_designCheck`.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-061529-b14-tests: lake build Tools.ShippingMemOnly Tests.Compiler.NoPortsMemOnlyCounterTest Tests.Compiler.NoPortsMemOnlySyncTest Tests.Compiler.NoPortsMemOnlyTwoTest Tests.Compiler.NoPortsMemOnlyAtProbe 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=937787392
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (581 jobs).
```
```
20261013-061621-b14-alltests: lake build Tests.AllTests Tests.Compiler.NoPortsMemOnlyAtProbe 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=427659264
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1210 jobs).
```

## Log excerpts (b14-tests)

```
est.lean:117:0: NOPORTS MEMONLY DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: nDecl=3, binders=10, call entries [SparkleMem.combo.4.8], argument lets [[1,
est.lean:571:0: NOPORTS MEMONLY [Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPorts0]: the depth-0 endpoint of a MEMORY-ONLY parent without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents — by hand (memCounter_data: MemOnlyData; memCounter_runFacts, memCounter_outsG0, memCounter_kidsMemG, memCounter_designP0: Tools.ShippingMemOnly.memOnly_* at depth 0). Its boundary is ChildBnd of the run's start world in place of the old True (ADDED); MachineCloses (all worlds) is STILL a binder
est.lean:584:0: NOPORTS MEMONLY ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_sv0: 5 — [Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true,
est.lean:584:0: NOPORTS MEMONLY ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPorts0: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w]
est.lean:584:0: NOPORTS MEMONLY AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPorts0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid (memKid_facts, kidsM_*, core_callStmtM) and the hand lemmas [Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_entry,
.lean:42:0: NOPORTS MEMONLY DATA Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: nDecl=3, binders=10, call entries [SparkleMem.sync.3.5], argument lets [[1,
.lean:243:0: NOPORTS MEMONLY [Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPorts0]: the depth-0 endpoint of a MEMORY-ONLY parent without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents — by hand (syncNarrow_data: MemOnlyData; syncNarrow_runFacts, syncNarrow_outsG0, syncNarrow_kidsMemG, syncNarrow_designP0: Tools.ShippingMemOnly.memOnly_* at depth 0). Its boundary is ChildBnd of the run's start world in place of the old True (ADDED); MachineCloses (all worlds) is STILL a binder
.lean:256:0: NOPORTS MEMONLY ANTECEDENTS Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_sv0: 5 — [Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true,
.lean:256:0: NOPORTS MEMONLY ANTECEDENTS Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPorts0: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w]
.lean:256:0: NOPORTS MEMONLY AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPorts0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid (memKid_facts, kidsM_*, core_callStmtM) and the hand lemmas [Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_entry,
lean:43:0: NOPORTS MEMONLY DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: nDecl=3, binders=12, call entries [SparkleMem.combo.4.8,
lean:244:0: NOPORTS MEMONLY [Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPorts0]: the depth-0 endpoint of a MEMORY-ONLY parent without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents — by hand (twoMems_data: MemOnlyData; twoMems_runFacts, twoMems_outsG0, twoMems_kidsMemG, twoMems_designP0: Tools.ShippingMemOnly.memOnly_* at depth 0). Its boundary is ChildBnd of the run's start world in place of the old True (ADDED); MachineCloses (all worlds) is STILL a binder
lean:257:0: NOPORTS MEMONLY ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_sv0: 5 — [Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true,
lean:257:0: NOPORTS MEMONLY ANTECEDENTS Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPorts0: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w]
lean:257:0: NOPORTS MEMONLY AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPorts0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid (memKid_facts, kidsM_*, core_callStmtM) and the hand lemmas [Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_entry,
lean:31:0: NOPORTS MEMONLY AT PROBE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: GENERATED Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0; its statement mentions [Tools.ShippingChildInv.MachineClosesAt,
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
  (Sparkle.Compiler.Elab.synthesizeCombinational `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter) mctx
  mref cctx cref w (b, design) w'
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
  Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData.shape
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0: NOT ALLOWED binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
  Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData.shape
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
```
