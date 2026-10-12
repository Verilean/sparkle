# Verification record: `grandH` boundary closed (round par/a-14, the part that built)

Tree: poc 099dacf0 + from par/a-14 (614c2e5e) ONLY `Tools/ShippingBoundaryClose.lean`,
`Tools/ShippingLeafKidFacts.lean`, `Tests/Compiler/NoPortsGrandHBTest.lean`,
`Tests/Compiler/BoundaryCloseBaseProbe.lean`, the append to `docs/parallel/A-remaining.md`; two `lean_lib`
entries; one import in `Tests/AllTests.lean`. Worker files unchanged.

## Established

`grandH.machine_design_noPortsNR1_closedB` (from the built `…_closed` by `#machine_boundary_close`): the
boundary antecedent is `ChildBnd mref cref w` only. Its former conjuncts `MachineDefines midH`, `True` and the
∀-contexts conjunct (`EntryDefines rcH` in every context where `midH` is synthesised) are DERIVED from the
binders through `EntryDefines.ctx`; no binder added. Premise listing: run, `MachineDefines grandH`,
`MachineDefines midH`, `EntryDefines rcH`, `ChildBnd` — all ALLOWED; goal-gap theorem
`…_closedB_gap` generated with no gap hypothesis. Together with 099dacf0: against
`grandH.machine_design_svNR1` no check premise and no NOT-ALLOWED premise remains, for this one declaration
(register parent, depth 1, child `midH` with a register and a one-output call of gate child `rcH`;
per-declaration decided data conditions; runtime boundary; `DesignSV` of the module list, not the SV string,
not `#sim`).

## Probe only (BoundaryCloseBaseProbe: target-built, logs, not in AllTests, nothing claimed)

On the base closed endpoints of `grandH`, `mixD1`, `topD2`, `grand` the same command derives the ∀-contexts
conjuncts and KEEPS the check premises (`shipsHierCheck`, `designCheck`, `outsCheck`, `kidsMaskedN`).
`mixDeep` (no closed form): two ∀-contexts conjuncts are KEPT, not derived.

## NOT built in this round (left on par/a-14, returned to the worker with the errors)

- `NoPortsMixD1Test`: asserts/decides for 2 call entries; measured `[midH, midH, cnt, cnt]`; decide-only data
  not `noncomputable`. `NoPortsMixD1BTest` not reached. Nothing is claimed for `mixD1`.
- `Tools/ShippingNoPortsKidsCommand.lean`: parse error at 657 (`← getEnv` outside `do`).
  `NoPortsKidsFamilyTest` not reached.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-045608-a14-tests: lake build Tools.ShippingBoundaryClose Tests.Compiler.NoPortsGrandHBTest Tools.ShippingLeafKidFacts Tests.Compiler.NoPortsMixD1Test Tests.Compiler.NoPortsMixD1BTest Tests.Compiler.BoundaryCloseBasePro
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=1021235200
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-045715-a14-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=836055040
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1188 jobs).
```

## Log excerpts (a14-tests)

```
info: Tests/Compiler/NoPortsGrandHBTest.lean:59:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB from Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed
KEPT (allowed): Tools.ShippingChildInv.ChildBnd mref cref w
DERIVED from the binders: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData.shape
DERIVED from the binders: True
DERIVED from the binders: ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
  Tools.ShippingChildInv.ChildRanIn mref cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH mctx' cctx' →
    ∀ (wc : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      Tools.ShippingChildInv.ChildBnd mref cref wc →
        Tools.ShippingChildInv.ChildBnd mref cref wc ∧
          Tools.ShippingInlineSoundness.EntryDefines mctx' mref cctx' cref
            `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
            Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue
info: Tests/Compiler/NoPortsGrandHBTest.lean:63:0: GOALGAP Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB_gap from Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB
ALLOWED     binder: Tools.ShippingEntrySoundness.RunsTo
  (Sparkle.Compiler.Elab.synthesizeCombinational `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH) mctx mref
  cctx cref w (b, design) w'
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machineData.shape
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData.shape
ALLOWED     binder: Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue
ALLOWED     kid_0: Tools.ShippingChildInv.ChildBnd mref cref w
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB: ALLOWED     binder hr : Tools.ShippingEntrySoundness.RunsTo
  (Sparkle.Compiler.Elab.synthesizeCombinational `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH) mctx mref
  cctx cref w (b, design) w'
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machineData.shape
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB: ALLOWED     binder hR_Sparkle_Tests_Compiler_ShippingMachineDepthHTest_midH : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData.shape
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB: ALLOWED     binder hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB: ALLOWED     antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
info: Tests/Compiler/NoPortsGrandHBTest.lean:136:0: NOPORTS GRANDH BOUNDARY Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB (from the built Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed by Tools.ShippingBoundaryClose: the boundary's conjuncts MachineDefines midH, True and the ∀
8463:error: Tests/Compiler/NoPortsMixD1Test.lean:91:0: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1: the call entries are [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
8467:error: Tests/Compiler/NoPortsMixD1Test.lean:124:7: failed to compile definition, compiler IR check failed at `dM`. Error: unknown join point 'block_0'
8802:error: Tests/Compiler/NoPortsMixD1Test.lean:128:7: failed to compile definition, compiler IR check failed at `dC`. Error: unknown join point 'block_0'
9137:error: Tests/Compiler/NoPortsMixD1Test.lean:132:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'dC', which is 'noncomputable'
9138:error: Tests/Compiler/NoPortsMixD1Test.lean:135:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'dC', which is 'noncomputable'
9139:error: Tests/Compiler/NoPortsMixD1Test.lean:140:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'dC', which is 'noncomputable'
9140:error: Tests/Compiler/NoPortsMixD1Test.lean:143:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'dC', which is 'noncomputable'
9141:error: Tests/Compiler/NoPortsMixD1Test.lean:147:52: Tactic `decide` proved that the proposition
9144:error: Tests/Compiler/NoPortsMixD1Test.lean:185:14: Type mismatch
9151:error: Tests/Compiler/NoPortsMixD1Test.lean:345:0: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1 uses a non-standard axiom: sorryAx
9152:error: Tests/Compiler/NoPortsMixD1Test.lean:362:0: Tests.Compiler.NoPortsMixD1Test.mixD1_tables uses a non-standard axiom: sorryAx
9200:error: Tools/ShippingNoPortsKidsCommand.lean:657:13: Nested action `← getEnv` must be nested inside a `do` expression.
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:33:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR1_closedB from Sparkle.Tests.Compiler.ShippingMachineDe
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:36:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2_closedB from Sparkle.Tests.Compiler.ShippingMachineDe
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:39:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR1_closedB from Sparkle.Tests.Compiler.ShippingDesignSVTest.mi
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:42:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2_closedB from Sparkle.Tests.Compiler.ShippingDesignSVTest.mi
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:45:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR2_closedB from Sparkle.Tests.Compiler.ShippingDesignSVTest.to
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:48:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3_closedB from Sparkle.Tests.Compiler.ShippingDesignSVTest.to
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 3
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 3
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:51:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_svNR2B from Sparkle.Tests.Compiler.ShippingChildBoundaryTe
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
KEPT (NOT ALLOWED, not derived): ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
info: Tests/Compiler/BoundaryCloseBaseProbe.lean:54:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_svNR2_closedB from Sparkle.Tests.Compiler.ShippingMachineSeqTes
KEPT (NOT ALLOWED, not derived): Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b = true
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
KEPT (NOT ALLOWED, not derived): Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true
```
