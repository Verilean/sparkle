# Verification record: `mixD1` (round par/a-14, second build)

Tree: poc 0dde44d6 + from par/a-14 (42b47bd2) `Tests/Compiler/NoPortsMixD1Test.lean`,
`Tests/Compiler/NoPortsMixD1BTest.lean`, the append to `docs/parallel/A-remaining.md`; one import in
`Tests/AllTests.lean`. Worker files unchanged. No new Tools file in this commit.

## Established

`mixD1` (register parent, depth 1; children: `midH` — a register and a one-output call of gate child `rcH` —
and the leaf register machine `cnt`; measured call entries `[midH, midH, cnt, cnt]`), by hand over
`OneOutKid.facts`, `leafKid_facts` and the `kids_*` theorems:
- against `mixD1.machine_design_svNR1` the premises `shipsHierCheck`, `kidsMaskedN`, `designCheck`, `outsCheck`
  are absent from `mixD1.machine_design_noPortsNR1(_closed)`; `EntryDefines rcH` at the run's contexts is a
  binder ADDED to the open form;
- `mixD1.machine_design_noPortsNR1_closedB` (by `#machine_boundary_close`): under the existentials only
  `ChildBnd`; premises: run, `MachineDefines mixD1`, `midH`, `cnt`, `EntryDefines rcH`, `ChildBnd`;
  0 NOT ALLOWED; goal-gap theorem with no gap hypothesis.
Scope: this one declaration; per-declaration decided data conditions; runtime boundary; `DesignSV` of the
module list, not the SV string, not `#sim`.

## NOT included

The generator `Tools/ShippingNoPortsKidsCommand.lean` elaborated, but `NoPortsKidsFamilyTest` FAILED: it
refused `grandH` / `mixD1` because it classified the grandchild `rcH` as a machine (`rcH.machineData` exists
next to its gate constants). Returned to the worker; nothing generated counts.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-045914-a14b-tests: lake build Tests.Compiler.NoPortsMixD1Test Tests.Compiler.NoPortsMixD1BTest Tools.ShippingNoPortsKidsCommand Tests.Compiler.NoPortsKidsFamilyTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=1035108352
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-050024-a14b-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=850579456
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1191 jobs).
```

## Log excerpts (a14b-tests)

```
info: Tests/Compiler/NoPortsMixD1Test.lean:90:0: NOPORTS MIXD1 DATA Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1: nDecl=1, call entries [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
info: Tests/Compiler/NoPortsMixD1Test.lean:333:0: NOPORTS MIXD1 [Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1, Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed]: the depth endpoint of a parent with a child with calls of its own AND a leaf register machine child, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mixD1_tables: OneOutKid.facts of midH, leafKid_facts of cnt; mixD1_runFacts, mixD1_outsG1, mixD1_maskedG, mixD1_designP1: Tools.ShippingKidFacts.kids_*); one binder ADDED against the open base endpoint: the reflection of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH at the run's contexts
info: Tests/Compiler/NoPortsMixD1Test.lean:350:0: NOPORTS MIXD1 AUDIT Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1 and Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed on standard axioms, with Tools.ShippingLeafKidFacts.leafKid_facts, OneOutKid.facts, the kids_* theorems and the hand lemmas mixD1_tables, mixD1_runFacts, mixD1_outsG1, mixD1_maskedG, mixD1_designP1. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR1 mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: 5 proposition binders — the run and the reflections of [Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1,
info: Tests/Compiler/NoPortsMixD1BTest.lean:45:0: NOPORTS MIXD1 BOUNDARY Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closedB (from Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed by Tools.ShippingBoundaryClose; nothing assumed, the same binders) and Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closedB_gap on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; 14 binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsMixD1Test; the run, the reflections of mixD1 / midH / cnt / rcH at the run's contexts and ChildBnd at the start world remain premises.
info: Tests/Compiler/NoPortsMixD1BTest.lean:37:0: BOUNDARY CLOSE Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closedB from Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed
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
DERIVED from the binders: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape
8600:error: Tests/Compiler/NoPortsKidsFamilyTest.lean:47:0: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: the callee Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH's callee Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH is a machine (generated for a GATE grandchild only: g.gate_full / g.gate_kidK)
8601:error: Tests/Compiler/NoPortsKidsFamilyTest.lean:51:0: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1: the callee Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH's callee Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH is a machine (generated for a GATE grandchild only: g.gate_full / g.gate_kidK)
8607:error: Tests/Compiler/NoPortsKidsFamilyTest.lean:65:2: Unknown constant `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed`
8608:error: Tests/Compiler/NoPortsKidsFamilyTest.lean:69:2: Unknown constant `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closedB`
8609:error: Tests/Compiler/NoPortsKidsFamilyTest.lean:72:0: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_regen: missing — the compare path did not rebuild Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1
```

## Addendum: the generator `#machine_no_ports_kids` (par/a-14 4f0db48a), built

After the worker's second repair (grandchild classified as the built one-output generator does: `gate_peel`
present ⇒ gate child), `Tools.ShippingNoPortsKidsCommand` and `Tests.Compiler.NoPortsKidsFamilyTest` build.
The family test is TARGET-BUILT ONLY (it creates the same `mixD1.*` constants as the hand tests, which are
the ones in AllTests). Nothing more is removed by it: `grandH` and `parent` are rebuilt and `isDefEq` the
existing statements, `mixD1` is generated in a separate import closure, `topD2` / `mixDeep` / `grand` are
REFUSED (callee has calls of its own under the general closing).

```
20261013-050126-a14c-family: lake build Tools.ShippingNoPortsKidsCommand Tests.Compiler.NoPortsKidsFamilyTest 
result=success
exit=0
memory_peak_file=902324224
20261013-050222-a14c-alltests: lake build Tests.AllTests Tests.Compiler.NoPortsKidsFamilyTest 
result=success
exit=0
memory_peak_file=134316032
Build completed successfully (1193 jobs).
lean:47:0: NOPORTS KIDS Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH at depth 1: REBUILT Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1: statement isDefEq the existing one (proof kept as Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_regen); REBUILT Sparkle.Tests.Compiler.ShippingMachineDepthHTe
lean:51:0: NOPORTS KIDS Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 at depth 1: GENERATED Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1; GENERATED Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1_closed (closing: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.closes_deep). Callees: [Sparkle.Tests.Compiler.Ship
lean:54:0: NOPORTS KIDS REFUSED Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 at depth 2: Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2: the callee Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 has calls of its own under the GENERAL closing (instFields ≠ []): KidFacts of such a child is not derived (unit U3: topD2, mixDeep, grand)
lean:56:0: NOPORTS KIDS REFUSED Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep at depth 2: Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep: the callee Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 has calls of its own under the GENERAL closing (instFields ≠ []): KidFacts of such a child is not derived (unit U3: topD2, mixDeep, grand)
lean:58:0: NOPORTS KIDS REFUSED Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand at depth 2: Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand: the callee Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid has calls of its own under the GENERAL closing (instFields ≠ []): KidFacts of such a child is not derived (unit U3: topD2, mixDeep, grand)
lean:61:0: NOPORTS KIDS Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent at depth 1: REBUILT Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noPortsNR1: statement isDefEq the existing one (proof kept as Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noPortsNR1_regen); REBUILT Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.ma
lean:72:0: NOPORTS KIDS FAMILY: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH — COMPARE path, both statements rebuilt by the generator and isDefEq the hand ones (nothing new removed). Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 — GENERATED: Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_noPortsNR1 and Sparkle.Tests.Compiler.ShippingDesignSVT
```
