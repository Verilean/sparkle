# Verification record: `mid`, `callerInner`, `grandH` (round par/a-13)

Tree: poc e260bf3f + the files of par/a-13 (8543a0ac) + five `lean_lib` entries + three imports in
`Tests/AllTests.lean`. Integrator change to worker files: three shape assertions (NoPortsMidTest:148,
NoPortsGrandHTest:133,135) compared the reader's call entries with `[c]`; the data is `[c, c]` (one entry
per projected field), so the first build failed THERE (run a13-tests, exit 1; all Tools files and the
endpoints had built). They now compare the distinct callees. No proof was changed.

## Established (built, standard axioms by the tests' audits)

- `mid` (register parent, leaf register machine child `cnt`): against `mid.machine_design_svNR1` the premises
  `shipsHierCheck`, `kidsMaskedN`, `designCheck`, `outsCheck` are absent from
  `mid.machine_design_noPortsNR1(_closed)`; closed form: run, `MachineDefines mid`, `MachineDefines cnt`,
  `ChildBnd`; 0 NOT ALLOWED. Nothing follows for `grand`, which calls `mid`.
- `callerInner` (register parent, gate child `pick`): against `callerInner.machine_design_svHR` the four
  premises `shipsHierHCheck`, `kidsComb`, `designCheck`, `outsCheck` are absent from
  `callerInner.machine_design_svH_full(_closed)`; closed form "other" NONE.
- `grandH` (register parent; child `midH` has a register AND a one-output call of the gate child `rcH`;
  depth 1; by hand over the new general lemmas): against `grandH.machine_design_svNR1` the premises
  `shipsHierCheck`, `kidsMaskedN`, `designCheck`, `outsCheck` are absent from
  `grandH.machine_design_noPortsNR1(_closed)`.
  NOT an empty gap: the boundary antecedent is classified NOT ALLOWED — it is `ChildBnd ∧ MachineDefines midH ∧
  ∀ contexts in which midH is synthesised, ChildBnd → ChildBnd ∧ EntryDefines rcH` — INHERITED unchanged from
  `grandH.machine_design_svNR1`, not removed, no goal-gap theorem generated. One binder is ADDED to the
  open form against the open base endpoint: `EntryDefines rcH` at the run's contexts (already a binder of the
  base closed endpoint).

New general statements (Tools/): `ShippingKidsSelf.core_kids_self`, `core_kidsPass_deep`, `core_kidsMaskedN_top`,
`ShippingOneOutKid.OneOutKid` (+ `.core`, `.check`, `.facts`), `ShippingKidFacts.KidFacts` (+ `kids_runFacts`,
`_outsCheck`, `_maskedN`, `_designCheck`), `ShippingCallsChildPorts.core_calls_ports₁`, `ShippingChildMapCongr`.

Scope unchanged: one declaration each, register parent, depth 1, per-declaration decided data conditions,
runtime boundary, `DesignSV` of the module list (not the SV string, not `#sim`), not all successful inputs.
Not done: generator for the `grandH` shape (`scopeP` still refuses), `mixD1` (needs `LeafKid → KidFacts`),
`topD2` / `mixDeep` / `grand`, memory children, parents without a register.
`RemainingProbeTest` creates the same `mid.*` / `callerInner.*` constants: it stays target-only and must
never be imported together with these tests.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-042023-a13-tests: lake build Tests.Compiler.NoPortsMidTest Tests.Compiler.OneOutCallerInnerTest Tools.ShippingChildMapCongr Tools.ShippingKidsSelf Tools.ShippingCallsChildPorts Tools.ShippingKidFacts Tools.ShippingOneOutKid Tests.Compiler.NoPortsGrandHTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=exit-code
exit=1
memory_peak_file=994144256
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
error: build failed
```
```
20261013-043505-a13-tests2: lake build Tests.Compiler.NoPortsMidTest Tests.Compiler.OneOutCallerInnerTest Tests.Compiler.NoPortsGrandHTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=574853120
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (575 jobs).
```
```
20261013-043541-a13-alltests: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=571707392
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1186 jobs).
```

## Log excerpts

```
8424:error: Tests/Compiler/NoPortsMidTest.lean:143:0: Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid: the call entries are [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
8425- Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt], expected [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt]
--
8490:error: Tests/Compiler/NoPortsGrandHTest.lean:125:0: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: the call entries are [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
8491- Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH], expected [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH]
info: Tests/Compiler/NoPortsGrandHTest.lean:515:0: NOPORTS GRANDH [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1, Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed]: the depth endpoint of a parent whose child has calls of its own, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (grandH_runFacts, grandH_outsG1, grandH_maskedG, grandH_designP1: Tools.ShippingKidFacts.kids_* over OneOutKid midH); one binder ADDED against the base endpoint: the reflection of Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH at the run's contexts
info: Tests/Compiler/NoPortsGrandHTest.lean:532:0: NOPORTS GRANDH AUDIT Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH: Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1 and Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed on standard axioms, with the general theorems of Tools.ShippingChildMapCongr / KidsSelf / CallsChildPorts / KidFacts / OneOutKid and the hand lemmas midH_kid, grandH_kids, grandH_runFacts, grandH_outsG1, grandH_maskedG, grandH_designP1. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR1 mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: 4 proposition binders — the run and the reflections of [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
info: Tests/Compiler/NoPortsMidTest.lean:136:0: NOPORTS TWO Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid: Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_noPortsNR1, Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_noPortsNR1_closed and Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_noPortsNR1_closed_gap on standard axioms, with Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_runFacts, _outsG1, _maskedG, _designG1, _designK1, _portsG, _designP1, Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_closes_at and machine_leafKid of [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt]; no endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_svNR1 (generated in this file) mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck; NO gap hypothesis; 12 binders and antecedents of the closed endpoint listed, 0 NOT ALLOWED; a MachineDefines binder per called declaration. Call entries [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
info: Tests/Compiler/NoPortsMidTest.lean:143:0: NOPORTS MID: Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid — nDecl=2, slots=1, call entries [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt] (a leaf register machine), instFields=[n,
info: Tests/Compiler/OneOutCallerInnerTest.lean:140:0: ONEOUT FAMILY Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner: Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner (Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots, _outChars, _outScalar, _callArgs at the numerals of Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.oneout_kidIns, _entries) and for the callees [Sparkle.Tests.Compiler.ShippingMachineInstTest.pick] (gate_width, what #gate_child left) are conditions, not reductions; (2) runtime boundary premises that remain: the run of the entry, MachineDefines of Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner, ChildBnd, EntryDefines of the callees (open form: also MachineClosesAt); (3) the result depends on the compi
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed: ALLOWED     binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthH
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machineData.shape
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed: ALLOWED     binder hR_Sparkle_Tests_Compiler_ShippingMachineDepthHTest_midH : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData.shape
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed: ALLOWED     binder hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHT
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue
NOPORTS PREMISE Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed: NOT ALLOWED antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w ∧
  Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData.shape ∧
    True ∧
      ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
        Tools.ShippingChildInv.ChildRanIn mref cref `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH mctx' cctx' →
          ∀ (wc : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
            Tools.ShippingChildInv.ChildBnd mref cref wc →
              Tools.ShippingChildInv.ChildBnd mref cref wc ∧
                Tools.ShippingInlineSoundness.EntryDefines mctx' mref cctx' cref
                  `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
                  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue
```
