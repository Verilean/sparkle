# Verification record: `seqMem` closed — the closing of a parent with a memory child (round par/a-18)

Tree: poc f9b40d5b + the files of par/a-18 (40c41fd1) + two `lean_lib` entries + one import in
`Tests/AllTests.lean`. Integrator change to a worker file: ONE line of the test
(`NoPortsMemSeqMemClosedTest.lean:383`, the two `nomatch` lambdas inside `⟨…, …⟩` parenthesised; the first
build failed there, both Tools files had built). No statement changed.

## Established

`seqMem.machine_design_noPortsR0_closed`: the binder `MachineClosesAt seqMem` of the open form is gone,
replaced by the binder `MachineDefines cnt` at the run's contexts (ADDED; the same fact was already a
conjunct of the boundary). Premises: run, `MachineDefines seqMem`, `MachineDefines cnt`, and under the
existentials `ChildBnd ∧ MachineDefines cnt` — all ALLOWED; goal-gap theorem `…_closed_gap` with no gap
hypothesis. `#machine_boundary_close` reports nothing to close (no `_closedB`). With 4a0d8356: against
`seqMem.machine_design_svR0` neither a check premise nor a NOT-ALLOWED premise remains — the first
gap-free endpoint of a parent with a memory child (register parent, leaf register child `cnt` and one
memory placeholder, depth 0; decided data conditions; runtime boundary; `DesignSV` of the module list,
not the SV string, not `#sim`).

General theorems (Tools/ShippingMemClosesRun.lean, ShippingMemClosesKids.lean): `mapM_loop_allM`,
M1 `closeInstsGM_run_allM` (no `hnomem`; children as `Kid`), `ChildIfaceP` (name per entry, `memOk`,
`self`), `memIface`, `design_checksM`, `closeInstsG_of_kidsP`, M2 `machineClosesAt_of_kidsDM`; the OLD
statements re-derived from them (`closeInstsGM_run_all_again`, `design_checks_again`,
`machineClosesAt_of_kidsD_fromM`) — generalisations, not copies; old files unchanged.

Not done: a shared descendant together with a memory entry (`closeInstsGM_run_allMF`), a generator, the
closing of memory-only parents.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-062404-a18-tests: lake build Tools.ShippingMemClosesRun Tools.ShippingMemClosesKids Tests.Compiler.NoPortsMemSeqMemClosedTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=822476800
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-062455-a18b-tests: lake build Tests.Compiler.NoPortsMemSeqMemClosedTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=388120576
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (581 jobs).
```
```
20261013-062505-a18-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=425799680
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1212 jobs).
```

## Log excerpts

```
8526:error: Tests/Compiler/NoPortsMemSeqMemClosedTest.lean:383:12: Insufficient number of fields for `⟨...⟩` constructor: Constructor `And.intro` has 2 explicit field, but only 1 was provided
8527:error: Tests/Compiler/NoPortsMemSeqMemClosedTest.lean:473:0: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed uses a non-standard axiom: sorryAx
8532:error: Tests/Compiler/NoPortsMemSeqMemClosedTest.lean:495:0: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed_gap uses a non-standard axiom: sorryAx
8534:error: Tests/Compiler/NoPortsMemSeqMemClosedTest.lean:505:0: Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_disj uses a non-standard axiom: sorryAx
Test.lean:74:0: MEMCLOSES DATA Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem: nDecl=3, binders=10, call entries [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
Test.lean:473:0: MEMCLOSES [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed]: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0 with its binder MachineClosesAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem replaced by the premise of seqMem_closes (the reflection of cnt at the run's contexts) — the closing of a parent with a memory child, by Tools.ShippingMemCloses.machineClosesAt_of_kidsDM over closeInstsGM_run_allM
Test.lean:491:0: BOUNDARY CLOSE REFUSED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed: no conjunct of a not-allowed antecedent follows from the binders (nothing to close):
Test.lean:505:0: MEMCLOSES ANTECEDENTS Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w ∧
Test.lean:505:0: MEMCLOSES ANTECEDENTS Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed: 1 — [Tools.ShippingChildInv.ChildBnd mref cref w ∧
Test.lean:505:0: MEMCLOSES AUDIT Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed and Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed_gap on standard axioms, with Tools.ShippingMemCloses (mapM_loop_allM, closeInstsGM_run_allM, design_checksM, memIface, closeInstsG_of_kidsP, machineClosesAt_of_kidsDM; the old statements re-derived: closeInstsGM_run_all_again, design_checks_again, machineClosesAt_of_kidsD_fromM) and the hand lemmas of this file. seqMem_closes has ONE proposition premise, the reflection of Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt. Against Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0 (12 premises listed, 1 NOT ALLOWED: MachineClosesAt Sparkle.Tests.Compil
info: Tests/Compiler/NoPortsMemSeqMemClosedTest.lean:495:0: GOALGAP Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed_gap from Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed
ALLOWED     binder: Tools.ShippingEntrySoundness.RunsTo
  (Sparkle.Compiler.Elab.synthesizeCombinational `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem) mctx mref
  cctx cref w (b, design) w'
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
  Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData.shape
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape
ALLOWED     kid_0: Tools.ShippingChildInv.ChildBnd mref cref w ∧
  Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape
```
