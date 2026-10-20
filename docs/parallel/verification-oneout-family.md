# Verification record: one-output generator on callerTwice, callerD, callerNested, callerRep (real log excerpts)

Runs through `scripts/shipping-coverage/cgrun.sh` (memory.max 3 GiB, swap 0, one job) on the poc working tree holding exactly the files of the commit made right after. Incremental builds (unchanged modules replayed).

## run 20261013-020411-fam1

```
command: lake build Tools.ShippingOneOutGenCommand Tests.Compiler.OneOutFamilyTest 
result=success
exit=0
memory_peak_file=1053929472
memory_current_max_sampled=1043251200
max_concurrent_lean=1
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (562 jobs).
```

## run 20261013-020533-fam2

```
command: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=442253312
memory_current_max_sampled=442245120
max_concurrent_lean=1
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1168 jobs).
```

## ONEOUT GEN lines

```
info: Tests/Compiler/OneOutFamilyTest.lean:188:0: ONEOUT GEN caller: PRESENT [caller.machine_design_svH_full, caller.machine_design_svH_full_closed] — already present, statement verified against the generated lemmas (rebuilt, compared by isDefEq); the existing constant is recorded as built from OTHER lemmas ([svH_full lemmas: facts := Tests.Compiler.OneOutCallerTest.caller_factsH, typed := Tests.Compiler.OneOutCallerPortsTest.caller_hierTyped, design := Tests.Compiler.OneOutCallerPortsTest.caller_designFull, outs := Tests.Compiler.OneOutCallerTest.caller_outsH]); the proof rebuilt now from the generated lemmas is kernel-checked as caller.machine_design_svH_full_gen (same statement); [svH_full lemmas: facts := caller.machine_factsH, typed := caller.machine_hierTypedH, design := caller.machine_designFullH, outs := caller.machine_outsH]; closed form caller.machine_design_svH_full_closed (ad
info: Tests/Compiler/OneOutFamilyTest.lean:197:0: ONEOUT GEN callerTwice: GENERATED [callerTwice.machine_design_svH_full, callerTwice.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := callerTwice.machine_factsH, typed := callerTwice.machine_hierTypedH, design := callerTwice.machine_designFullH, outs := callerTwice.machine_outsH]; closed form callerTwice.machine_design_svH_full_closed (added or verified by closeEndpointAt); data conditions decided by the kernel for callerTwice: callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with callerTwice.oneout_kidIns = [[2, 8]], per entry the callee among [pick] with its argument widths and the result binder's width [8]; for the callees: ga
info: Tests/Compiler/OneOutFamilyTest.lean:207:0: ONEOUT GEN callerD: GENERATED [callerD.machine_design_svH_full, callerD.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := callerD.machine_factsH, typed := callerD.machine_hierTypedH, design := callerD.machine_designFullH, outs := callerD.machine_outsH]; closed form callerD.machine_design_svH_full_closed (added or verified by closeEndpointAt); data conditions decided by the kernel for callerD: callsOk 2, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with callerD.oneout_kidIns = [[2, 8]], per entry the callee among [pickD] with its argument widths and the result binder's width [8]; for the callees: gateSort.width, what #gate_child left. Th
info: Tests/Compiler/OneOutFamilyTest.lean:217:0: ONEOUT GEN callerNested: GENERATED [callerNested.machine_design_svH_full, callerNested.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := callerNested.machine_factsH, typed := callerNested.machine_hierTypedH, design := callerNested.machine_designFullH, outs := callerNested.machine_outsH]; closed form callerNested.machine_design_svH_full_closed (added or verified by closeEndpointAt); data conditions decided by the kernel for callerNested: callsOk 2, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with callerNested.oneout_kidIns = [[2, 8]], per entry the callee among [pick] with its argument widths and the result binder's width [8]; for the c
info: Tests/Compiler/OneOutFamilyTest.lean:227:0: ONEOUT GEN callerRep: GENERATED [callerRep.machine_design_svH_full, callerRep.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := callerRep.machine_factsH, typed := callerRep.machine_hierTypedH, design := callerRep.machine_designFullH, outs := callerRep.machine_outsH]; closed form callerRep.machine_design_svH_full_closed (added or verified by closeEndpointAt); data conditions decided by the kernel for callerRep: callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with callerRep.oneout_kidIns = [[2, 8], [2, 8]], per entry the callee among [pick] with its argument widths and the result binder's width [8]; for the callees: gateSort.width
info: Tests/Compiler/OneOutFamilyTest.lean:239:0: ONEOUT GEN callerInner: REFUSED (no callerInner.machine_ships_hierHR: run #machine_design_svHR callerInner first)
```

## Premise lists of the closed forms (non-data lines) and "other" of the open forms

```
ONEOUT FULL PREMISE callerTwice.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pick
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerTwice
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerTwice.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerD.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pickD
ONEOUT FULL PREMISE callerD.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerD.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerD
ONEOUT FULL PREMISE callerD.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerD
ONEOUT FULL PREMISE callerD.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerD.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerD.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerD.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerD
ONEOUT FULL PREMISE callerD.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerD.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerD.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pickD
ONEOUT FULL PREMISE callerNested.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pick
ONEOUT FULL PREMISE callerNested.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerNested.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerNested.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerNested
ONEOUT FULL PREMISE callerNested.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerNested.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerNested.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE callerNested.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
ONEOUT FULL PREMISE callerNested.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerNested.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerNested.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerRep.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pick
ONEOUT FULL PREMISE callerRep.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational `callerRep) mctx mref cctx cref w
ONEOUT FULL PREMISE callerRep.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerRep callerRep.machineData.shape
ONEOUT FULL PREMISE callerRep.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `callerRep callerRep.machineData.shape
ONEOUT FULL PREMISE callerRep.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerRep.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerRep.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational `callerRep) mctx mref cctx cref w
ONEOUT FULL PREMISE callerRep.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `callerRep callerRep.machineData.shape
ONEOUT FULL PREMISE callerRep.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE callerRep.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE callerRep.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
```

## Audit / summary lines of the family test

```
info: Tests/Compiler/OneOutFamilyTest.lean:220:0: GOALGAP callerNested.machine_design_svH_full_closed_gap from callerNested.machine_design_svH_full_closed
info: Tests/Compiler/OneOutFamilyTest.lean:220:0: ONEOUT FAMILY callerNested: callerNested.machine_design_svH_full (13 lines; other: the closing premise only) and callerNested.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of callerNested.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap callerNested.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for callerNested (callerNested.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots, _outChars, _outScalar, _callArgs at the numerals of call
info: Tests/Compiler/OneOutFamilyTest.lean:230:0: ONEOUT FULL PREMISE callerRep.machine_closes_at: data | binder mctx._@.Tests.Compiler.ShippingCallsCloseTest.1262007418._hygCtx._hyg.8 : Lean.Meta.Context
info: Tests/Compiler/OneOutFamilyTest.lean:230:0: ONEOUT FULL PREMISE callerRep.machine_design_svH_full: data | binder mctx : Lean.Meta.Context
info: Tests/Compiler/OneOutFamilyTest.lean:230:0: ONEOUT FULL PREMISE callerRep.machine_design_svH_full_closed: data | binder mctx : Lean.Meta.Context
info: Tests/Compiler/OneOutFamilyTest.lean:230:0: GOALGAP callerRep.machine_design_svH_full_closed_gap from callerRep.machine_design_svH_full_closed
info: Tests/Compiler/OneOutFamilyTest.lean:230:0: ONEOUT FAMILY callerRep: callerRep.machine_design_svH_full (13 lines; other: the closing premise only) and callerRep.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of callerRep.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap callerRep.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for callerRep (callerRep.oneout_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots, _outChars, _outScalar, _callArgs at the numerals of callerRep.oneout_kidIns, 
info: Tests/Compiler/OneOutFamilyTest.lean:241:0: ONEOUT FAMILY: callerInner REFUSED, nothing left under its names. Out of scope in this round and not run: callerMix, callerABA (two called declarations: name-separation premises may appear in the closed form).
```
