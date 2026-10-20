# Verification record: `grand` and `topD2` at depth 2 (round par/a-15)

Tree: poc c46b309c + the files of par/a-15 (4c96d59d, worker files unchanged) + three `lean_lib` entries +
two imports in `Tests/AllTests.lean`. All seven targets built at the first attempt.

## Established (built; standard axioms by the tests' audits)

- `grand` (register parent; callee `mid` — a register machine whose own calls of the leaf register machine
  `cnt` are tied by the GENERAL closing; depth 2; by hand over `GenKid`, `leafKid_facts`, `kids_*`):
  against `grand.machine_design_svNR2` the premises `shipsHierCheck`, `kidsMaskedN`, `designCheck`, `outsCheck`
  are absent from `grand.machine_design_noPortsNR2(_closed)`; one binder ADDED to the open form
  (`MachineDefines cnt` at the run's contexts). `…NR2_closedB` (by `#machine_boundary_close`): under the
  existentials only `ChildBnd`; premises run, `MachineDefines grand` / `mid` / `cnt`, `ChildBnd`; 0 NOT ALLOWED;
  goal-gap theorem with no gap hypothesis.
- `topD2` (register parent; callee `mid2`, whose callee `midH` has a one-output call of gate child `rcH`;
  the depth-2 endpoint ONLY): against `topD2.machine_design_svNR2` the same four premises are absent from
  `topD2.machine_design_noPortsNR2(_closed)`; `…NR2_closedB`: premises run, `MachineDefines topD2` / `mid2` /
  `midH`, `EntryDefines rcH`, `ChildBnd`; 0 NOT ALLOWED; goal-gap theorem with no gap hypothesis.

New general statements (Tools/): `ShippingCallsPortsG.core_calls_portsG`, `kids_designCheck_in`,
`ShippingGenKid.GenKid` (+ `.check`, `.facts`, `.masked`), `ShippingOneOutKidDepth.factsN`.

Scope: one declaration each; per-declaration decided data conditions; runtime boundary; `DesignSV` of the
module list, not the SV string, not `#sim`; not all successful inputs.
Not done: `topD2.machine_design_svNR3` (depth 3), `mixDeep` (no closed base form), a generator for the
general-closing child, memory children, parents without a register.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-052217-a15-tests: lake build Tools.ShippingCallsPortsG Tools.ShippingGenKid Tests.Compiler.NoPortsGrandTest Tests.Compiler.NoPortsGrandBTest Tools.ShippingOneOutKidDepth Tests.Compiler.NoPortsTopD2Test Tests.Compiler.NoPortsTopD2BTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=1058873344
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (581 jobs).
```
```
20261013-052313-a15-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=441511936
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1198 jobs).
```

## Log excerpts (a15-tests)

```
info: Tests/Compiler/NoPortsGrandHTest.lean:515:0: NOPORTS GRANDH [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1, Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed]: the depth endpoint of a parent whose child has calls of its own, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (grandH_runFacts, grandH_outsG1, grandH_maskedG, grandH_designP1: Tools.ShippingKidFacts.kids_* over OneOutKid midH); one binder ADDED against the base endpoint: the reflection of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH at the run's contexts
info: Tests/Compiler/NoPortsGrandHTest.lean:532:0: NOPORTS GRANDH AUDIT Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1 and Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed on standard axioms, with the general theorems of Tools.ShippingChildMapCongr / KidsSelf / CallsChildPorts / KidFacts / OneOutKid and the hand lemmas midH_kid, grandH_kids, grandH_runFacts, grandH_outsG1, grandH_maskedG, grandH_designP1. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR1 mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: 4 proposition binders — the run and the reflections of [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
info: Tests/Compiler/NoPortsGrandHBTest.lean:136:0: NOPORTS GRANDH BOUNDARY Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB (from the built Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed by Tools.ShippingBoundaryClose: the boundary's conjuncts MachineDefines midH, True and the ∀-contexts conjunct about midH's own boundary are DERIVED from the binders by EntryDefines.ctx — nothing assumed, the binders are those of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed) and Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB_gap on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; 13 binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsGrandHTest (one declaration, depth 1, per-declaration decided data conditions, compiler guards with fallback, DesignSV of the module list, not the SV string, not #sim); the run, the reflections of grandH / midH / rcH at the run's contexts and ChildBnd at the start world remain premises.
info: Tests/Compiler/NoPortsGrandTest.lean:116:0: NOPORTS GRAND DATA Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand: nDecl=1, call entries [Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid,
info: Tests/Compiler/NoPortsGrandTest.lean:523:0: NOPORTS GRAND [Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2, Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closed]: the depth-2 endpoint of a parent whose child's own calls are tied by the general closing, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mid_kid: GenKid of the child, KidFacts of its leaf callee at the depths 1 and 2 by leafKid_facts; grand_kids: GenKid.facts; grand_runFacts, grand_outsG2, grand_maskedG, grand_designP2: Tools.ShippingKidFacts.kids_* at depth 2); one binder ADDED against the open base endpoint: the reflection of Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt at the run's contexts
info: Tests/Compiler/NoPortsGrandTest.lean:540:0: NOPORTS GRAND AUDIT Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand: Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2 and Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closed on standard axioms, with the general theorems of Tools.ShippingCallsPortsG / ShippingGenKid, Tools.ShippingLeafKidFacts.leafKid_facts, the kids_* theorems and the hand lemmas mid_kid, grand_kids, grand_runFacts, grand_outsG2, grand_maskedG, grand_designP2. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_svNR2 mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: 4 proposition binders — the run and the reflections of [Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand,
info: Tests/Compiler/NoPortsTopD2Test.lean:99:0: NOPORTS TOPD2 DATA Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: nDecl=1, call entries [Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2,
info: Tests/Compiler/NoPortsTopD2Test.lean:615:0: NOPORTS TOPD2 [Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2, Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closed]: the depth-2 endpoint of a parent whose child (general closing) has a child with a one-output call of a gate, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mid2_kid: GenKid; KidFacts of midH at depth 1 by OneOutKid.facts and at depth 2 by Tools.ShippingOneOutKidDepth.factsN; topD2_kids: GenKid.facts; topD2_runFacts, topD2_outsG2, topD2_maskedG, topD2_designP2: Tools.ShippingKidFacts.kids_* at depth 2); two binders ADDED against the open base endpoint: the reflections of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH and Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH at the run's contexts
info: Tests/Compiler/NoPortsTopD2Test.lean:641:0: NOPORTS TOPD2 AUDIT Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2 and Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closed on standard axioms, with the general theorems of Tools.ShippingCallsPortsG / ShippingGenKid / ShippingOneOutKidDepth, OneOutKid.facts, the kids_* theorems and the hand lemmas midH_names, mid2_kid, topD2_kids, topD2_runFacts, topD2_outsG2, topD2_maskedG, topD2_designP2. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR2 mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: 5 proposition binders — the run and the reflections of [Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
info: Tests/Compiler/NoPortsGrandBTest.lean:48:0: NOPORTS GRAND BOUNDARY Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand: Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB (from Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closed by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB_gap on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; 13 binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsGrandTest; the run, the reflections of grand / mid / cnt at the run's contexts and ChildBnd at the start world remain premises.
info: Tests/Compiler/NoPortsTopD2BTest.lean:50:0: NOPORTS TOPD2 BOUNDARY Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB (from Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closed by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB_gap on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; 14 binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsTopD2Test (depth 2 only); the run, the reflections of topD2 / mid2 / midH / rcH at the run's contexts and ChildBnd at the start world remain premises.
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB: ALLOWED     binder hR_Sparkle_Tests_Compiler_ShippingMachineSeqTest_mid : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB: ALLOWED     binder hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_noPortsNR2_closedB: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB: ALLOWED     binder hR_Sparkle_Tests_Compiler_ShippingDesignSVTest_mid2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB: ALLOWED     binder hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB: ALLOWED     binder hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR2_closedB: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
```
