# Verification record: At-form endpoints of the five memory-only parents; the all-worlds closing (round par/b-15)

Tree: poc 710ed31f + the files of par/b-15 (d6b44b8a) + one `lean_lib` + six imports in
`Tests/AllTests.lean`; the superseded log probe `NoPortsMemOnlyAtProbe.lean` removed (it created the same
constant as the new memCounter test). Integrator change to a worker file: two lines of
`NoPortsMemOnlyAtLib.lean` (`let mut nProp : Nat := 0`, `let mut nBad : Nat := 0`; the first build failed
there on `OfNat MessageData`). No statement changed.

## Established

For each of `memCounter`, `syncNarrow`, `twoMems`, `mixedMems` (combo + sync entries), `memWide`: the NEW
statement `f.machine_design_noPortsR0` (depth 0) with premises run, `MachineDefines f`,
`MachineClosesAt f`, and under the existentials `ChildBnd`. The audit (throws otherwise): no checker
constant; EXACTLY ONE premise NOT ALLOWED, `MachineClosesAt f`; no closed form; standard axioms.
This is not "the base with premises removed": the base `f.machine_design_sv0` has the four checks
(`shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0`), boundary `True` and the ALL-WORLDS
`MachineCloses f`; the new statement has none of the four checks, `ChildBnd` instead of `True`, and the At
closing instead of the all-worlds one. NOT gap-free: `MachineClosesAt f` remains.

All-worlds closing (decision (b) with a caveat): `not_machineCloses_of_synthNone` — `MachineCloses` of a
shape with calls is contradicted by one harness run accepted by `closeLets` that ends in a world where
`sparkleChildSynth` reads `none` (the closing reads that ref before looking at any child, memory entries
included; by reading, Elab.lean 5209). CONDITIONAL: the existence of such a run is not proved, so
`¬ MachineCloses` is not a theorem. Consequence recorded: the closing premise of `f.machine_design_sv0` /
`f.machine_design_noPorts0` cannot be discharged; those endpoints stay uncounted.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-062539-b15-tests: lake build Tests.Compiler.NoPortsMemOnlyAtLib Tests.Compiler.NoPortsMemOnlyAtMemCounterTest Tests.Compiler.NoPortsMemOnlyAtSyncNarrowTest Tests.Compiler.NoPortsMemOnlyAtTwoMemsTest Tests.Compiler.NoPo
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=922513408
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-062623-b15b-tests: lake build Tests.Compiler.NoPortsMemOnlyAtLib Tests.Compiler.NoPortsMemOnlyAtMemCounterTest Tests.Compiler.NoPortsMemOnlyAtSyncNarrowTest Tests.Compiler.NoPortsMemOnlyAtTwoMemsTest Tests.Compiler.NoPo
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=533139456
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (586 jobs).
```
```
20261013-062639-b15-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=430661632
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1220 jobs).
```

## Log excerpts

```
8625:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:174:21: failed to synthesize instance of type class
8632:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:188:20: failed to synthesize instance of type class
8639:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:188:11: failed to synthesize instance of type class
8643:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:175:20: failed to synthesize instance of type class
8650:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:191:17: failed to synthesize instance of type class
8657:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:191:9: failed to synthesize instance of type class
8661:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:179:17: failed to synthesize instance of type class
8665:error: Tests/Compiler/NoPortsMemOnlyAtLib.lean:181:18: failed to synthesize instance of type class
t.lean:28:0: NOPORTS MEMONLY ALL-WORLDS DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: call entries [SparkleMem.combo.4.8], instFields=[out], lets=4, slots=2
t.lean:28:0: NOPORTS MEMONLY ALL-WORLDS DATA Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: call entries [SparkleMem.sync.3.5], instFields=[out], lets=4, slots=2
t.lean:28:0: NOPORTS MEMONLY ALL-WORLDS DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: call entries [SparkleMem.combo.4.8,
t.lean:28:0: NOPORTS MEMONLY ALL-WORLDS DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems: call entries [SparkleMem.combo.4.8,
t.lean:28:0: NOPORTS MEMONLY ALL-WORLDS DATA Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide: call entries [SparkleMem.combo.6.16], instFields=[out], lets=4, slots=2
t.lean:73:0: NOPORTS MEMONLY ALL-WORLDS AUDIT: on standard axioms, MachineCloses of a shape with calls (memory-only shapes included) is contradicted by ONE harness run accepted by closeLets that ends in a world where sparkleChildSynth reads none (not_machineCloses_of_synthNone; instantiated at memCounter). CONDITIONAL: the existence of such a run is NOT proved (not derivable in the model) — so ¬ MachineCloses is not a theorem; what is recorded is that the all-worlds closing premise of f.machine_design_sv0 / f.machine_design_noPorts0 cannot be discharged, and that no endpoint changes. The memory entries themselves read nothing (pure md); the read that fails is the closing's first statement.
eTest.lean:237:0: NOPORTS MEMONLY AT AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide: Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid and the hand lemmas [Tests.Compiler.NoPortsMemOnlyAt
emsTest.lean:258:0: NOPORTS MEMONLY AT AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid and the hand lemmas [Tests.Compiler.
rrowTest.lean:66:0: NOPORTS MEMONLY AT AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPortsR0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid and the hand lemmas [Tests.Compiler.NoPortsM
sTest.lean:66:0: NOPORTS MEMONLY AT AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid and the hand lemmas [Tests.Compiler.NoPorts
nterTest.lean:65:0: NOPORTS MEMONLY AT AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0 on standard axioms, with the general theorems of Tools.ShippingMemOnly (kidsMem_of, core_kidsMemM, memOnly_*) over the built Tools.ShippingMemKid and the hand lemmas [Tests.Compile
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0: NOT ALLOWED binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
```
