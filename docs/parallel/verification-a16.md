# Verification record: `topD2` at depth 3 (round par/a-16, the part that built)

Tree: poc fcabc921 + from par/a-16 (3b70e5eb) ONLY `Tests/Compiler/NoPortsTopD2N3Test.lean`,
`Tests/Compiler/NoPortsTopD2N3BTest.lean`, the append to `docs/parallel/A-remaining.md`; one import in
`Tests/AllTests.lean`. Worker files unchanged. No new Tools file.

## Established

`topD2` at depth 3 (by hand: `GenKid.facts` at n = 2, `factsN`, the built `mid2_kid`, `topD2_runFacts`,
`topD2_maskedG`): against `topD2.machine_design_svNR3` the premises `shipsHierCheck`, `kidsMaskedN`,
`designCheck`, `outsCheck` are absent from `topD2.machine_design_noPortsNR3(_closed)`; `…NR3_closedB`:
premises run, `MachineDefines topD2` / `mid2` / `midH`, `EntryDefines rcH`, `ChildBnd`; 0 NOT ALLOWED;
goal-gap theorem with no gap hypothesis. Scope as before (one declaration, decided data conditions, runtime
boundary, `DesignSV` of the module list, not the SV string, not `#sim`).

## NOT built (left on par/a-16, returned to the worker; nothing claimed)

- `NoPortsMixDeepTest`: `#machine_closes_deep mixDeep` succeeded with 7 premises — 4 reflections and
  name-separation conditions (∀ k < insts.length, a name is not among the descendants' declaration names).
  The generated `mixDeep.machine_design_noPortsNR2_closed` therefore carries binders that are neither the
  run nor a reflection, and the test's audit threw at line 443. These are decidable data conditions that
  the closing generator discharged for `grandH` / `topD2` and did not for `mixDeep`.
- `Tools/ShippingNoPortsDeepCommand.lean`: elaboration error at 403 (`.oneOut` pattern on a value of
  unknown type). `NoPortsDeepFamilyTest` not reached.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-054250-a16-tests: lake build Tests.Compiler.NoPortsTopD2N3Test Tests.Compiler.NoPortsTopD2N3BTest Tests.Compiler.NoPortsMixDeepTest Tests.Compiler.NoPortsMixDeepBTest Tools.ShippingNoPortsDeepCommand Tests.Compiler.NoPortsDeepFamilyTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=1103097856
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-054413-a16-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=833622016
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1200 jobs).
```

## Log excerpts (a16-tests)

```
info: Tests/Compiler/NoPortsTopD2N3Test.lean:76:0: NOPORTS TOPD2 N3 DATA Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: nDecl=1, call entries [Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2,
info: Tests/Compiler/NoPortsTopD2N3Test.lean:282:0: NOPORTS TOPD2 N3 [Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3, Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closed]: the depth-3 endpoint of topD2 without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mid2_kid2: GenKid at n = 2 from the fields of the BUILT mid2_kid, KidFacts of midH at depth 3 by Tools.ShippingOneOutKidDepth.factsN … 2; topD2_kids3: GenKid.facts; topD2_outsG3, topD2_designP3: kids_* at depth 3; the BUILT topD2_runFacts and topD2_maskedG, whose statements have no depth); two binders ADDED against the open base endpoint: the reflections of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH and Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH at the run's contexts
info: Tests/Compiler/NoPortsTopD2N3Test.lean:308:0: NOPORTS TOPD2 N3 AUDIT Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3 and Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closed on standard axioms, with GenKid.facts at n = 2, Tools.ShippingOneOutKidDepth.factsN, the kids_* theorems and the hand lemmas mid2_kid2, topD2_kids3, topD2_outsG3, topD2_designP3 (and the BUILT mid2_kid, topD2_runFacts, topD2_maskedG). No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3 mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. DesignSV at depth 3 in both. Closed form: 5 proposition binders — the run and the reflections of [Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
info: Tests/Compiler/NoPortsTopD2N3BTest.lean:37:0: NOPORTS TOPD2 N3 BOUNDARY Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB (from Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closed by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB_gap on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; 14 binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsTopD2N3Test (depth 3); the run, the reflections of topD2 / mid2 / midH / rcH at the run's contexts and ChildBnd at the start world remain premises.
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB: ALLOWED     binder hR_Sparkle_Tests_Compiler_ShippingDesignSVTest_mid2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB: ALLOWED     binder hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB: ALLOWED     binder hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_noPortsNR3_closedB: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
8859:error: Tests/Compiler/NoPortsMixDeepTest.lean:443:0: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_noPortsNR2_closed: a binder that is neither the run nor a reflection:
8932:error: Tools/ShippingNoPortsDeepCommand.lean:403:10: Invalid dotted identifier notation: The expected type of `.oneOut`
8935:error: Tools/ShippingNoPortsDeepCommand.lean:403:2: Invalid pattern(s): `g` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
info: Tests/Compiler/NoPortsMixDeepTest.lean:134:0: NOPORTS MIXDEEP CLOSING Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.closes_deep: generated by #machine_closes_deep, standard axioms; 7 premises:
Tools.ShippingMachineEntry.MachineDefines mctx✝ mref✝ cctx✝ cref✝ `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData.shape
Tools.ShippingMachineEntry.MachineDefines mctx✝ mref✝ cctx✝ cref✝ `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData.shape
Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue
Tools.ShippingMachineEntry.MachineDefines mctx✝ mref✝ cctx✝ cref✝ `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape
```
