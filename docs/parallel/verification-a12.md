# Verification record: `midH` (one-output closing) and `two` (multi-output closing), round par/a-12

Tree: poc cc4cc69e + the files of par/a-12 (55030752, worker files unchanged) + two imports in
`Tests/AllTests.lean`. No new `Tools/` theorem: existing generators run on two declarations inside their
stated scope that had never been run. Runs through `cgrun.sh -m 3G` (swap 0, one job); excerpts are copied
from the run records.

## Established

- `midH` (register parent, gate child `rcH`, two parent outputs): against `midH.machine_design_svHR` the
  four check premises `shipsHierHCheck`, `kidsComb`, `designCheck`, `outsCheck` are absent from
  `midH.machine_design_svH_full(_closed)`; closed form "other" NONE. This is about `midH` as an entry;
  nothing is removed from `grandH`, `mixD1`, `topD2`, `mixDeep`, which call it.
- `two` (register parent, two DIFFERENT leaf register machine children `cnt`, `acc`): against
  `two.machine_design_svNR1` the premises `shipsHierCheck`, `kidsMaskedN`, `designCheck`, `outsCheck` are
  absent from `two.machine_design_noPortsNR1(_closed)`; closed form: run, `MachineDefines` of `two`, `cnt`,
  `acc`, `ChildBnd`. First elaboration of the several-callee branches of that chain.

Scope unchanged: one declaration each, register parent, depth 1, per-declaration decided data conditions,
runtime boundary, `DesignSV` of the module list (not the SV string, not `#sim`), not all successful inputs.

## Probe only (RemainingProbeTest: target-built, logs, NOT in AllTests, nothing claimed)

`mid` and `callerInner` went through the generators in the probe (lines below); they need proper tests
before any premise counts as removed. `loopParent` FAILED at `#machine_design_svNR 1`. The refusals of
`grandH`, `mixD1`, `topD2`, `mixDeep`, `grand`, `seqMem`, `memCounter`, `engineOnce` are logged with reasons.
Census of everything still carrying check premises: `docs/parallel/A-remaining.md`.

## Run records

```
20261013-034457-a12-tests: lake build Tests.Compiler.OneOutMidHTest Tests.Compiler.NoPortsTwoTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=513449984
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (564 jobs).
```
```
20261013-034517-a12-alltests: lake build Tests.AllTests Tests.Compiler.RemainingProbeTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=676573184
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1179 jobs).
```

## Log excerpts

```
info: Tests/Compiler/OneOutMidHTest.lean:91:0: ONEOUT GEN Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH: GENERATED [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_design_svH_full, Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_factsH, typed := Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_hierTypedH, design := Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_desig
info: Tests/Compiler/OneOutMidHTest.lean:94:0: ONEOUT FAMILY Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machine_design_svH_full_closed_gap: 4 lines, none
info: Tests/Compiler/OneOutMidHTest.lean:104:0: ONEOUT MIDH: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH — nDecl=2, slots=1, call entries [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH] (gate child), instFields=[], outputs [n,
info: Tests/Compiler/NoPortsTwoTest.lean:180:0: NOPORTS TWO Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed and Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed_gap on standard axioms, with Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_runFacts, _outsG1, _maskedG, _designG1, _designK1, _portsG, _designP1, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_closes_at and machine_leafKid of [Sparkle.Tests.
info: Tests/Compiler/NoPortsTwoTest.lean:100:0: NOPORTS [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1,
 Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed]: the depth endpoint without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents; check antecedent left: none (run facts by Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_runFacts, output check under the gate by Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_outs
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed: ALLOWED     binder hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed: ALLOWED     binder hR1 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_noPortsNR1_closed: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w ∧
n:126:0: REMAINING PROBE mid: #machine_endpoint (FAILED is expected when its endpoint already exists): FAILED — (kernel) constant has already been declared 'Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData'
n:130:0: REMAINING PROBE mid: #machine_design_svNR 1: OK
n:134:0: REMAINING PROBE mid: #machine_closes_at: OK
n:141:0: REMAINING PROBE Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid audit: OK — Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_noPortsNR1_closed passes the audit of NoPortsTwoTest (its NOPORTS TWO line above carries the scope)
n:148:0: REMAINING PROBE loopParent: #machine_design_svNR 1: FAILED — seq child Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL: Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machine_sound is not built from Tools.ShippingMachineAuto.machine_trace_of_data
n:152:0: REMAINING PROBE loopParent: #machine_closes_at: OK
n:156:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent at depth 1: Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent: no depth endpoint at depth 1 (Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_ships_hierNR1 is not there: run #machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent 1 fi
n:159:0: REMAINING PROBE Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent: no Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_design_noPortsNR1_closed (the open form Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_design_noPortsNR1 exists: no; the depth endpoint Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent
n:167:0: REMAINING PROBE callerInner: #machine_design_svHR: OK
n:171:0: REMAINING PROBE callerInner: #machine_closes_at: OK
n:175:0: REMAINING PROBE callerInner: #machine_oneout: OK
n:179:0: REMAINING PROBE Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner audit: OK — the audit of OneOutFamilyTest ran (its ONEOUT FAMILY line above carries the scope; a SKIPPED line there means no closed form)
n:187:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH at depth 1: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: the callee Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)
n:189:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 at depth 1: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1: the callee Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)
n:191:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 at depth 2: Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: the callee Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)
n:193:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep at depth 2: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep: the callee Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)
n:195:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand at depth 2: Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand: the callee Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)
n:197:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem at depth 1: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem: the callee SparkleMem.combo.4.8 is not a leaf register machine: it is a memory child (LeafKid is about a machine declaration's data)
n:199:0: NOPORTS REFUSED Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter at depth 0: Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: the callee SparkleMem.combo.4.8 is not a leaf register machine: it is a memory child (LeafKid is about a machine declaration's data)
n:201:0: NOPORTS REFUSED Sparkle.Tests.Compiler.MultiInstance.engineOnce at depth 1: Sparkle.Tests.Compiler.MultiInstance.engineOnce: parent without a register (core_portsMatch_raw_leaf asks d.shape.layout.slots ≠ []: the parent's clk and rst ports, which the connections of a sequential child are matched against, are derived from the parent's own register by core_clk)
```
