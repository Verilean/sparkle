# Verification record: `seqMem` — a parent with a memory child (round par/b-13)

Tree: poc de7d6d4d + the files of par/b-13 (9a263350, worker files unchanged) + three `lean_lib` entries +
one import in `Tests/AllTests.lean`. The first build (ac3197d2) failed in `Tools/ShippingMemKidFacts.lean` on
two syntax errors; the worker's repair built at the first attempt.

## Established

`seqMem` (register parent; children: the leaf register machine `cnt` AND a memory placeholder
`SparkleMem.combo.*`; depth 0): against `seqMem.machine_design_svR0` the premises `shipsHierCheck`,
`kidsMixed`, `designCheck … 0`, `outsCheck … 0` are absent from the OPEN form
`seqMem.machine_design_noPortsR0`. NOT gap-free: `MachineClosesAt seqMem` is still a binder (classified
NOT ALLOWED) and there is no closed form; the boundary antecedent is as before; no binder added.
First endpoint with a memory child whose check premises are derived.

How: the interface `KidFacts` is vacuous / false for a memory child (no declaration; `outsMaskedN` false of
the memory module; `kidCheck` at depth ≥ 1 false because `seqStmtOkI` rejects `.memory`), so a new interface
`KidFactsM` over `Kid` (memory placeholder OR real child) with `FlatOk`, `memKid_facts` for the built memory
module at depth 0, `kidFacts_toM`, `core_kidsMixedM`, `kidsM_*`.

## What this costs and what it does not give

- `Tools/ShippingMemKidCore.lean` and `Tools/ShippingMemKidPorts.lean` are SCRIPTED COPIES of 17 built
  `core_*` theorems with `hnomem` dropped and `RealChild` generalised to `Kid`. The old theorems are not
  derived from the new ones; unifying them is not done.
- Not removed for anything else: the memory-only parents `memCounter`, `twoMems`, `mixedMems`, `memWide`,
  `syncNarrow` keep `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0` and the old boundary (their
  endpoints come from another head; only a log probe was run).
- Missing (worker's statements): `closeInstsGM_run_all` without `hnomem` and `machineClosesAt_of_kidsD` for
  a memory child (closing), `core_kidsMemM` (memory-only parents), and a statement change of `designCheck`
  for a memory child at depth ≥ 1.

Scope: one declaration, decided data conditions, runtime boundary, `DesignSV` of the module list at depth 0,
not the SV string, not `#sim`.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-055426-b13-tests: lake build Tools.ShippingMemKidCore Tools.ShippingMemKidPorts Tools.ShippingMemKidFacts Tests.Compiler.NoPortsMemSeqMemTest Tests.Compiler.NoPortsMemDataProbe 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=941043712
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-055624-b13b-tests: lake build Tools.ShippingMemKidFacts Tests.Compiler.NoPortsMemSeqMemTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=357515264
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (577 jobs).
```
```
20261013-055644-b13b-alltests: lake build Tests.AllTests Tests.Compiler.NoPortsMemDataProbe 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=422117376
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1206 jobs).
```

## Log excerpts

```
8531:error: Tools/ShippingMemKidFacts.lean:344:30: Insufficient number of fields for `⟨...⟩` constructor: Constructor `And.intro` has 2 explicit field, but only 1 was provided
8532:error: Tools/ShippingMemKidFacts.lean:344:43: Missing eliminator: An eliminator must be provided when multiple induction targets are specified and no default eliminator has been registered
8545:error: Tools/ShippingMemKidFacts.lean:471:89: unexpected identifier; expected '}'
8546:error: Tools/ShippingMemKidFacts.lean:471:9: Fields missing: `inW`, `clk`, `check`
8547:error: Tools/ShippingMemKidFacts.lean:470:59: unsolved goals
ean:97:0: NOPORTS MEM DATA Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem: nDecl=3, binders=10, call entries [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
ean:474:0: NOPORTS MEM [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0]: the depth-0 endpoint of a parent with a sequential child AND a memory child, without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMixed antecedents — by hand (seqMem_kids: KidFactsM of cnt by leafKid_facts + kidFacts_toM, of the memory placeholder by memKid_facts; seqMem_runFacts, seqMem_outsG0, seqMem_mixedG, seqMem_designP0: Tools.ShippingMemKid.kidsM_* at depth 0). MachineClosesAt of the parent is STILL a binder; no binder added
ean:487:0: NOPORTS MEM ANTECEDENTS Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_svR0: 5 — [Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true,
ean:487:0: NOPORTS MEM ANTECEDENTS Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w ∧
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0: NOT ALLOWED binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w ∧
an:31:0: NOPORTS MEM PROBE DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: nDecl=3, binders=10, call entries [SparkleMem.combo.4.8], argument lets [[1,
an:31:0: NOPORTS MEM PROBE DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: nDecl=3, binders=12, call entries [SparkleMem.combo.4.8,
an:31:0: NOPORTS MEM PROBE DATA Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems: nDecl=3, binders=12, call entries [SparkleMem.combo.4.8,
an:31:0: NOPORTS MEM PROBE DATA Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide: nDecl=3, binders=10, call entries [SparkleMem.combo.6.16], argument lets [[1,
an:31:0: NOPORTS MEM PROBE DATA Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: nDecl=3, binders=10, call entries [SparkleMem.sync.3.5], argument lets [[1,
```
