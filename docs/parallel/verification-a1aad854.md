# Verification record for a015a6f7 and a1aad854 (excerpts of the real run logs)

Written by the integrator from the run directories under `~/sparkle-work/runs/` (outside the repository). Each run went through `scripts/shipping-coverage/cgrun.sh` (systemd --user scope, MemoryMax 3G, swap 0, one job). The tree built was the poc working tree holding exactly the files of the commit made right after the run (build-before-commit; staged files only). These `Tests.AllTests` runs are INCREMENTAL builds: unchanged modules were replayed from the build cache, so their memory peaks are small; the last full rebuilds of this line are the integration runs recorded in the commit messages of a9fd07ca, d0d68225, b7971f83 (peaks 2.57–2.69 GiB). No GitHub Actions run exists for these SHAs.

## run 20261013-013756-oo2

```
command: lake build Tools.ShippingOneOutSameRun Tools.ShippingOneOutCommand Tests.Compiler.OneOutCallerTest 
protect: unit=sparkle-oo2-20261013-013756 mainpid=1534237 cgroup=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/sparkle-oo2-20261013-013756.service self_cgroup=/user.slice/user-1000.slice/session-39.scope memory.max=3221225472 memory.high=2738040832 memory.swap.max=0 memory.oom.group=1
result=success
exit=0
memory_peak_file=910299136
memory_current_max_sampled=895619072
max_concurrent_lean=2
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (554 jobs).
```

## run 20261013-013840-oo3

```
command: lake build Tools.ShippingTypedWidthOk Tools.ShippingGatePorts Tools.ShippingOneOutConns Tests.Compiler.OneOutCallerPortsTest 
protect: unit=sparkle-oo3-20261013-013840 mainpid=1535128 cgroup=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/sparkle-oo3-20261013-013840.service self_cgroup=/user.slice/user-1000.slice/session-39.scope memory.max=3221225472 memory.high=2738040832 memory.swap.max=0 memory.oom.group=1
result=success
exit=0
memory_peak_file=576331776
memory_current_max_sampled=509767680
max_concurrent_lean=2
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (558 jobs).
```

## run 20261013-013856-ooall

```
command: lake build Tests.AllTests 
protect: unit=sparkle-ooall-20261013-013856 mainpid=1535432 cgroup=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/sparkle-ooall-20261013-013856.service self_cgroup=/user.slice/user-1000.slice/session-39.scope memory.max=3221225472 memory.high=2738040832 memory.swap.max=0 memory.oom.gro
result=success
exit=0
memory_peak_file=572182528
memory_current_max_sampled=557445120
max_concurrent_lean=1
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1164 jobs).
```

## run 20261013-014433-oo4

```
command: lake build Tools.ShippingOneOutFullCommand Tests.Compiler.OneOutCallerFullTest 
protect: unit=sparkle-oo4-20261013-014433 mainpid=1537022 cgroup=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/sparkle-oo4-20261013-014433.service self_cgroup=/user.slice/user-1000.slice/session-39.scope memory.max=3221225472 memory.high=2738040832 memory.swap.max=0 memory.oom.group=1
result=success
exit=0
memory_peak_file=792190976
memory_current_max_sampled=765374464
max_concurrent_lean=1
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (560 jobs).
```

## run 20261013-014518-oo5

```
command: lake build Tests.AllTests 
protect: unit=sparkle-oo5-20261013-014518 mainpid=1537858 cgroup=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/sparkle-oo5-20261013-014518.service self_cgroup=/user.slice/user-1000.slice/session-39.scope memory.max=3221225472 memory.high=2738040832 memory.swap.max=0 memory.oom.group=1
result=success
exit=0
memory_peak_file=419225600
memory_current_max_sampled=414060544
max_concurrent_lean=1
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1166 jobs).
```

## a015a6f7 — endpoint caller with two residual conditions (runs oo2, oo3, ooall)

```
info: Tests/Compiler/OneOutCallerTest.lean:269:0: SVHFREE GENERATED [Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_free,
info: Tests/Compiler/OneOutCallerTest.lean:279:0: ONEOUT PREMISES Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_free: 13 binders and antecedents listed; not a run / reflection / ChildBnd: 2; of them the residual antecedent: 1, holding 2 INDEPENDENT check conditions (hierTyped; portsMatchB)
info: Tests/Compiler/OneOutCallerTest.lean:279:0: ONEOUT PREMISES Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_free_closed: 13 binders and antecedents listed; not a run / reflection / ChildBnd: 1; of them the residual antecedent: 1, holding 2 INDEPENDENT check conditions (hierTyped; portsMatchB)
info: Tests/Compiler/OneOutCallerTest.lean:279:0: ONEOUT RESIDUAL caller: hierTyped=T portsMatchB=T (same run)
info: Tests/Compiler/OneOutCallerTest.lean:279:0: ONEOUT CROSS-CHECK caller (a second, separate core run; not what the claim rests on): modules equal to the first run's=T, its module post-processes to the first run's b=T, hierTyped=T portsMatchB=T
info: Tests/Compiler/OneOutCallerPortsTest.lean:250:0: ONEOUT WRITTEN caller: hierTyped (caller_hierTyped) and portsMatchB of the shipped module (caller_portsShipped) stated with premises the core run, the post-processing fact, caller's reflection and closing, ChildBnd, pick's reflection; data condi
```

## a1aad854 — endpoint caller without check premise (runs oo4, oo5)

```
info: Tests/Compiler/OneOutCallerFullTest.lean:83:0: SVHFULL GENERATED [Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_full,
 Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_full_closed]: the combinational endpoint with NO check antecedent and no residual (the trivially true residual discharged; none of the eight checker constants written in the statement or found by the premise expansion); [svH_f
info: Tests/Compiler/OneOutCallerFullTest.lean:89:0: @Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_full : ∀ {mctx : Lean.Meta.Context}
info: Tests/Compiler/OneOutCallerFullTest.lean:169:0: ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder mctx : Meta.Context
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder mref : ST.Ref IO.RealWorld Meta.State
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder cctx : Core.Context
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder cref : ST.Ref IO.RealWorld Core.State
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder w : Void IO.RealWorld
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder w' : Void IO.RealWorld
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder b : Sparkle.IR.AST.Module
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: data | binder design : Sparkle.IR.AST.Design
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `caller
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE caller.machine_design_svH_full_closed: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE caller.machine_design_svH_full: run | binder hr : Tools.ShippingEntrySoundness.RunsTo
ONEOUT FULL PREMISE caller.machine_design_svH_full: reflection | binder entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `caller
ONEOUT FULL PREMISE caller.machine_design_svH_full: other | binder closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref `caller
ONEOUT FULL PREMISE caller.machine_design_svH_full: ChildBnd | antecedent under the existentials : Tools.ShippingChildInv.ChildBnd mref cref w
ONEOUT FULL PREMISE caller.machine_design_svH_full: reflection | antecedent under the existentials : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
ONEOUT FULL PREMISE caller.machine_closes_at: reflection | binder hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx✝ mref✝ cctx✝ cref✝ `pick
info: Tests/Compiler/OneOutCallerFullTest.lean:93:0: GOALGAP caller.machine_design_svH_full_closed_gap from caller.machine_design_svH_full_closed
ALLOWED     binder: Tools.ShippingEntrySoundness.RunsTo
  (Sparkle.Compiler.Elab.synthesizeCombinational `caller) mctx mref cctx
  cref w (b, design) w'
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `caller
  caller.machineData.shape
ALLOWED     binder: Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref `pick
info: Tests/Compiler/OneOutCallerFullTest.lean:169:0: ONEOUT FULL caller: caller.machine_design_svH_full (13 lines; other: the closing premise only) and caller.machine_design_svH_full_closed (13 lines; other: NONE) — the combinational endpoint of caller with none of the four check premises of caller.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck) and no residual. SCOPE of this statement: (i) data conditions decided per declaration for caller (callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk caller.machineData 1 kidIns, the result binder's width 8) and for pick (gateSort.width = 8, what #gate_child left); (ii) runtime boundary premises that remain: the run of the entry, MachineDefines of caller, ChildBnd, EntryDefines of pick (open form: also MachineClosesAt); (iii) the result depends on the compiler's guards (checkedOptimize's fallback, deinline's guards, closeInsts' checks); (iv) the conclusion is about DesignSV (childMap D.modules) 0 (checkedOptimize b) — the module list, not the SV string, not #sim; (v) ONE declaration with a register, a gate child and a one-output closing: not slotless parents, not machine-route children, not all successful inputs. Standard axioms.
```

## cgroup limits as recorded by the runner (run oo5; the others have the same request)

```
unit=sparkle-oo5-20261013-014518 mainpid=1537858 cgroup=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/sparkle-oo5-20261013-014518.service self_cgroup=/user.slice/user-1000.slice/session-39.scope memory.max=3221225472 memory.high=2738040832 memory.swap.max=0 memory.oom.group=1 requested: max=3221225472 high=2738040832 swap=0 group=1 timeout=5000 threads=2 verified=yes 
```

## Axiom audit lines (run oo4)

```
info: Tests/Compiler/ShippingCallsCloseTest.lean:197:0: ONE-OUTPUT COMBINATIONAL CHILDREN CLOSED (gate children: caller, callerTwice, callerNested, callerD, midH, callerMix, callerRep, callerABA; slotless machine children: callerL, callerLN, hftByte): machine_design_svHR_closed reaches none of MachineCloses / MachineClosesAt / CallsPure / CallsClose / LetsClose (statement and every definition under it); standard axioms. Premises of caller.machine_closes_at: [Tools.ShippingInlineSoundness.EntryDefines
 caller.machine_design_svH_free_closed] (WRITTEN; a reduction only once built) — of the four check premises of caller.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck): kidsComb and outsCheck derived from the run; designCheck narrowed to portsMatchB of the shipped module; shipsHierHCheck narrowed to hierTyped of the full entry's module (hierBinds no longer asked). TWO INDEPENDENT residual conditions remain as premises: hierTyped=T, portsMatchB=T on (b, D) of one full run. Scope: caller has a register (slots ≠ []); one call entry of the gate child pick, one-output closing; slotless parents and other declarations not covered. Standard axioms.
info: Tests/Compiler/OneOutCallerPortsTest.lean:250:0: ONEOUT WRITTEN caller: hierTyped (caller_hierTyped) and portsMatchB of the shipped module (caller_portsShipped) stated with premises the core run, the post-processing fact, caller's reflection and closing, ChildBnd, pick's reflection; data conditions decided here: callArgsOk caller.machineData 1 kidIns (kidIns: the widths of the declared non-domain binders of pick), the result binder's width, pick.gateSort.width = 8. The endpoint caller.machine_design_svH_free is NOT regenerated: its two residual conditions are still premises. Standard axioms.
info: Tests/Compiler/OneOutCallerFullTest.lean:169:0: ONEOUT FULL caller: caller.machine_design_svH_full (13 lines; other: the closing premise only) and caller.machine_design_svH_full_closed (13 lines; other: NONE) — the combinational endpoint of caller with none of the four check premises of caller.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck) and no residual. SCOPE of this statement: (i) data conditions decided per declaration for caller (callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk caller.machineData 1 kidIns, the result binder's width 8) and for pick
```

## What these runs do NOT establish

- Scope: ONE declaration (`ShippingMachineInstTest.caller`: a parent with a register, the gate-route child `pick`, the one-output closing). Per-declaration data conditions are decided by `decide`; `RunsTo`, `MachineDefines`, `EntryDefines`, `ChildBnd` remain premises; the conclusion is about the `DesignSV` object of the module list, not the SV string, not `#sim`.
- UNRESOLVED (not complete, not claimed): the generalisation of the call-kind / length facts of the reader (R1, R5/`LenOk` of the returned state, P5) — blocked by the `partial` readers and `opaque` `Expr` operations; replacing the partial readers is a compiler change that has not been decided or started. Slotless parents, machine-route children, multi-output closings beyond `parent`/`chained`, all successful inputs.
- The isolated candidates `fix/wire-refs-build` (changes the output of the constructed declaration `dTop`; under investigation), `fix/wirewidth-local-build`, `fix/call-kinds` are not merged.
