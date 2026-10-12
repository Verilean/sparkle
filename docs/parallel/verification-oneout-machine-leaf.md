# Verification record: callerMix, callerABA (two gate callees) and callerL (slotless leaf machine child) — real log excerpts

Runs through `scripts/shipping-coverage/cgrun.sh` (memory.max 3 GiB, swap 0, one job) on the poc working tree holding exactly the files of the commit made right after. Incremental builds.

## run 20261013-030124-a10

```
command: lake build Tools.ShippingLeafOneOut Tests.Compiler.OneOutTwoCalleeTest Tests.Compiler.OneOutCallerLTest 
result=success
exit=0
memory_peak_file=977526784
memory_current_max_sampled=963960832
max_concurrent_lean=2
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (567 jobs).
```

## run 20261013-030207-a10all

```
command: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=553127936
memory_current_max_sampled=547037184
max_concurrent_lean=1
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1172 jobs).
```

## Summary lines of the two tests

```
info: Tests/Compiler/OneOutCallerLTest.lean:521:0: SVHFULL GENERATED [callerL.machine_design_svH_full,
info: Tests/Compiler/OneOutCallerLTest.lean:534:0: ONEOUT MACHINE-LEAF callerL: callerL.machine_design_svH_full (13 lines; other: the closing premise only) and callerL.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of callerL.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap callerL.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. The child's premise is its MACHINE reflection (MachineDefines of pickByteH), not EntryDefines. SCOPE of this statement: (1) data conditions decided per declaration by the kernel — for callerL: callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [] (the parent has a register), output width / name / scalar conditions, no memory callee, callWidthsStrict against pickByteH's layout outputs (the result binder's width), callArgsOk against pickByteH's declared widths; for pickByteH (the fields of pickByteH_leaf): ok, the body equation, callsOk and no late domain binder at nIn, insts = [] (a leaf), the slot count, output width / name / scalar conditions, gateCallsOk at nIn, lets ≠ 0, slots = [] (slotless), the one output out, and its generated closing pickByteH.machine_closes — conditions, not reductions; (2) runtime boundary premises that remain: the run of the entry, MachineDefines of callerL, MachineDefines of pickByteH, ChildBnd (open form: also MachineClosesAt); (3) the result depends on the compiler's guards (checkedOptimize's fallback, deinline's guards, closeInsts' checks, mergeChecked's validation of the child's mer
info: Tests/Compiler/OneOutTwoCalleeTest.lean:127:0: ONEOUT GEN callerMix: GENERATED [callerMix.machine_design_svH_full, callerMix.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := callerMix.machine_factsH, typed := callerMix.machine_hierTypedH, design := callerMix.machine_designFullH, outs := callerMix.machine_outsH]; closed form callerMix.machine_design_svH_full_closed (added or verified by closeEndpointAt); data conditions decided by the kernel for callerMix: callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with callerMix.oneout_kidIns = [[2, 8], [2, 8]], per entry the callee among [pick, pickD] with its argument widths and the result binder's width [8, 8]; for the callees: gateSort.width, what #gate_child left. These are conditions, not reductions; the run, MachineDefines, EntryDefines and ChildBnd remain premises
info: Tests/Compiler/OneOutTwoCalleeTest.lean:130:0: ONEOUT FAMILY callerMix: callerMix.machine_design_svH_full (14 lines; other: the closing premise only) and callerMix.machine_design_svH_full_closed (15 lines; other: NONE) — none of the four check premises of callerMix.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap callerMix.machine_design_svH_full_closed_gap: 5 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for callerMix (callerMix.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots, _outChars, _outScalar, _callArgs at the numerals of callerMix.oneout_kidIns, _entries) and for the callees [pick,
info: Tests/Compiler/OneOutTwoCalleeTest.lean:130:0: ONEOUT TWO-CALLEE callerMix: callerMix.machine_closes_at has 2 proposition binders, all EntryDefines ([pick,
info: Tests/Compiler/OneOutTwoCalleeTest.lean:142:0: ONEOUT GEN callerABA: GENERATED [callerABA.machine_design_svH_full, callerABA.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := callerABA.machine_factsH, typed := callerABA.machine_hierTypedH, design := callerABA.machine_designFullH, outs := callerABA.machine_outsH]; closed form callerABA.machine_design_svH_full_closed (added or verified by closeEndpointAt); data conditions decided by the kernel for callerABA: callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with callerABA.oneout_kidIns = [[2, 8], [2, 8], [2, 8]], per entry the callee among [pick, pickD] with its argument widths and the result binder's width [8, 8]; for the callees: gateSort.width, what #gate_child left. These are conditions, not reductions; the run, MachineDefines, EntryDefines and ChildBnd remain premises
info: Tests/Compiler/OneOutTwoCalleeTest.lean:145:0: ONEOUT FAMILY callerABA: callerABA.machine_design_svH_full (14 lines; other: the closing premise only) and callerABA.machine_design_svH_full_closed (15 lines; other: NONE) — none of the four check premises of callerABA.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap callerABA.machine_design_svH_full_closed_gap: 5 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for callerABA (callerABA.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots, _outChars, _outScalar, _callArgs at the numerals of callerABA.oneout_kidIns, _entries) and for the callees [pick,
info: Tests/Compiler/OneOutTwoCalleeTest.lean:145:0: ONEOUT TWO-CALLEE callerABA: callerABA.machine_closes_at has 2 proposition binders, all EntryDefines ([pick,
```

## Non-data premise lines of the closed forms and "other" of the open forms

```
ONEOUT FULL PREMISE callerL.machine_closes_at: reflection | binder hR0 : Tools.ShippingMachineEntry.MachineDefines mctx✝ mref✝ cctx✝ cref✝
ONEOUT FULL PREMISE callerL.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerL.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerL
ONEOUT FULL PREMISE callerL.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerL
ONEOUT FULL PREMISE callerL.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerL.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerL.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerL.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerL
ONEOUT FULL PREMISE callerL.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerL.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerL.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerMix.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pick
ONEOUT FULL PREMISE callerMix.machine_closes_at: reflection | binder hR1 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pickD
ONEOUT FULL PREMISE callerMix.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerMix.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerMix
ONEOUT FULL PREMISE callerMix.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerMix
ONEOUT FULL PREMISE callerMix.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerMix.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerMix.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerMix
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: reflection | binder hR1 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerMix.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerABA.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pick
ONEOUT FULL PREMISE callerABA.machine_closes_at: reflection | binder hR1 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pickD
ONEOUT FULL PREMISE callerABA.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational `callerABA) mctx mref cctx cref w
ONEOUT FULL PREMISE callerABA.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerABA callerABA.machineData.shape
ONEOUT FULL PREMISE callerABA.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerABA callerABA.machineData.shape
ONEOUT FULL PREMISE callerABA.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerABA.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerABA.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational `callerABA) mctx mref cctx cref w
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerABA callerABA.machineData.shape
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: reflection | binder hR1 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerABA.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
```

## Scope

One declaration each; a parent WITH a register; the one-output closing; children: gate children (callerMix, callerABA) or ONE slotless leaf machine child with the single output `out` (callerL). Per-declaration data conditions are decided by the kernel and are not reductions; the run, `MachineDefines`, `EntryDefines`, `ChildBnd` remain premises; the result depends on the compiler guards with fallback; the conclusion is about `DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module list, not the SV string, not `#sim`. Not covered: slotless parents, machine children with registers or calls, several outputs, `callerLN`, `hftByte`, all successful inputs.
