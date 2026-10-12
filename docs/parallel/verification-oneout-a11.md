# Verification record: one-output closing, `callerLN` and `hftByte` (round par/a-11)

Tree: poc 85ebb9fd + the files of par/a-11 (bbbb9d8d, worker files unchanged) + two `lean_lib` entries in
`lakefile.lean` + `import Tests.Compiler.OneOutAnyFamilyTest` in `Tests/AllTests.lean`. All runs through
`scripts/shipping-coverage/cgrun.sh -m 3G` (swap 0, one job). Excerpts below are copied from the run
records under `~/sparkle-work/runs/`; nothing was rebuilt for this record.

## What the runs establish

Against `f.machine_design_svHR`, the four check premises `shipsHierHCheck`, `kidsComb`, `designCheck`,
`outsCheck` are absent from `f.machine_design_svH_full` / `_closed` for

- `callerLN` (child `pickByteH`, a slotless leaf machine child with the one output `out`),
- `hftByte` (child `Sparkle.IP.Net.HTTP.httpGetByte`, same kind, implicit domain binder),

each both by hand lemmas (`OneOutCallerLNTest`, `OneOutHftByteTest`; target-built only) and by the generator
`#machine_oneout_any` (`OneOutAnyFamilyTest`; in AllTests). The hand tests and the family test define the
same constant names and are never in one import closure. Closed-form premises: the run, `MachineDefines f`,
`MachineDefines` of the child, `ChildBnd`; "other" NONE. For `callerL` and `callerMix` nothing more is
removed: the generator rebuilds a statement `isDefEq` the existing endpoint.

## Scope (unchanged)

One declaration each; a parent with a register; the one-output closing; data conditions decided per
declaration by the kernel (not removed); `MachineDefines` / `ChildBnd` / the runtime boundary remain;
the conclusion is about `DesignSV` of the module list, not the SV string, not `#sim`. The audit function
throws on any non-standard axiom, so a built test means standard axioms for the audited names.
Not covered: slotless parents (paper analysis only, A-oneout.md §13), machine children with registers or
calls (refused by the generator; that refusal branch has no test), a parent mixing a gate callee and a
machine-leaf callee (never elaborated), multi-output, all successful inputs.

## Run records

### 20261013-032741-a11-tools
```
command: lake build Tools.ShippingLeafOneOutGen Tools.ShippingOneOutAnyGenCommand Tests.Compiler.OneOutLeafAudit 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=1194766336
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (567 jobs).
```

### 20261013-032907-a11-tests
```
command: lake build Tests.Compiler.OneOutCallerLNTest Tests.Compiler.OneOutHftByteTest Tests.Compiler.OneOutAnyFamilyTest 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=562896896
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (573 jobs).
```

### 20261013-032947-a11-alltests
```
command: lake build Tests.AllTests 
memory.max=3221225472
memory.swap.max=0
verified=yes
result=success
exit=0
memory_peak_file=441348096
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
Build completed successfully (1176 jobs).
```

## Log excerpts (a11-tests, log.txt)

```
8329:info: Tests/Compiler/OneOutCallerLTest.lean:534:0: ONEOUT MACHINE-LEAF callerL: Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. The child's premise is its MACHINE reflection (MachineDefines of pickByteH), not EntryDefines. SCOPE of this statement: (1) d
8330:ℹ [567/573] Built Tests.Compiler.OneOutCallerLNTest (1.0s)
8712:info: Tests/Compiler/OneOutCallerLNTest.lean:382:0: ONEOUT MACHINE-LEAF Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN: Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. Machine-route callees (premise: MachineDefines of the child): [Sparkle
9115:ℹ [572/573] Built Tests.Compiler.OneOutHftByteTest (2.4s)
9116:info: Tests/Compiler/OneOutHftByteTest.lean:116:0: ONEOUT DATA Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte: nDecl=2 nIn=3 slots=4 lets=30 insts=[Sparkle.IP.Net.HTTP.httpGetByte args(let indices)=[27]] instFields=[] outs=[out:8] binders(width or dom)=[8, 1, 8, 8, 3, 1, 6, 8, 8, 8, 8, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 6, 6, 1, 1, 1, 6, 6, 8]
9117:info: Tests/Compiler/OneOutHftByteTest.lean:116:0: ONEOUT DATA Sparkle.IP.Net.HTTP.httpGetByte: nDecl=2 nIn=2 slots=0 lets=12 insts=[] instFields=[] outs=[out:8] binders(width or dom)=[dom, 6, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]
9599:info: Tests/Compiler/OneOutHftByteTest.lean:634:0: ONEOUT MACHINE-LEAF Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte: Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. Machine-route callees (premise: MachineDefines of the child): [Sparkle.IP.Net.HTTP.htt
9600:ℹ [573/573] Built Tests.Compiler.OneOutAnyFamilyTest (5.8s)
9601:info: Tests/Compiler/OneOutAnyFamilyTest.lean:110:0: ONEOUT ANY Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL: PRESENT [Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full, Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full_closed] — already present, statement verified against the generated lemmas (rebuilt, compared by isDefEq); the existing constant is recorded as built from OTHER lemmas ([svH_full lemmas: facts := Tests.Compiler.OneOutCallerLTest.callerL_factsH, typed := Tests.Compiler.OneOutCallerLTest.callerL_hierTyped, design := Tests.Compiler.OneOutCallerLTest.callerL_designFull, outs := Tests.Compiler.OneOutCallerLTest.callerL_outsH]); the proof rebuilt now from the gen
9648:info: Tests/Compiler/OneOutAnyFamilyTest.lean:113:0: ONEOUT ANY FAMILY Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL: Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full_closed_gap: the theorem exists already, not generated again. The endpoint existed (hand lemmas); the statement rebu
9649:info: Tests/Compiler/OneOutAnyFamilyTest.lean:121:0: ONEOUT ANY Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN: GENERATED [Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full, Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_factsH, typed := Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_hierTypedH, design := Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_designFullH, outs := Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_out
9709:info: Tests/Compiler/OneOutAnyFamilyTest.lean:124:0: ONEOUT ANY FAMILY Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN: Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. Machine-route callees (premise: MachineDefines of the child): [Sparkle.
9710:info: Tests/Compiler/OneOutAnyFamilyTest.lean:132:0: ONEOUT ANY Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte: GENERATED [Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full, Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed] — the combinational endpoint with NO check antecedent and no residual, from generated lemmas; [svH_full lemmas: facts := Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_factsH, typed := Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_hierTypedH, design := Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_designFullH, outs := Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_outsH]; closed form Spar
9764:info: Tests/Compiler/OneOutAnyFamilyTest.lean:135:0: ONEOUT ANY FAMILY Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte: Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. Machine-route callees (premise: MachineDefines of the child): [Sparkle.IP.Net.HTTP.htt
9765:info: Tests/Compiler/OneOutAnyFamilyTest.lean:143:0: ONEOUT ANY Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix: PRESENT [Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_design_svH_full, Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_design_svH_full_closed] — already present, statement verified against the generated lemmas (rebuilt, compared by isDefEq), recorded lemmas equal; [svH_full lemmas: facts := Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_factsH, typed := Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_hierTypedH, design := Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_designFullH, outs := Sparkle.Tests.Compiler.ShippingPremiseEvalTest.ca
9816:info: Tests/Compiler/OneOutAnyFamilyTest.lean:146:0: ONEOUT ANY FAMILY Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix: Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_design_svH_full (14 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_design_svH_full_closed (15 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix.machine_design_svH_full_closed_gap: the theorem exists already, not generated again. Machine-route callees (premise: MachineDefines of the 
9818:info: Tests/Compiler/OneOutAnyFamilyTest.lean:157:0: ONEOUT ANY Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner: REFUSED (no Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner.machine_ships_hierHR: run #machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner first)
9819:info: Tests/Compiler/OneOutAnyFamilyTest.lean:159:0: ONEOUT ANY FAMILY: Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner REFUSED, nothing left under its names.

info: Tests/Compiler/OneOutHftByteTest.lean:634:0: GOALGAP Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed_gap from Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machine_design_svH_full_closed
ALLOWED     binder: Tools.ShippingEntrySoundness.RunsTo
  (Sparkle.Compiler.Elab.synthesizeCombinational `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte) mctx mref cctx
  cref w (b, design) w'
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte
  Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte.machineData.shape
ALLOWED     binder: Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.IP.Net.HTTP.httpGetByte
  Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape
ALLOWED     kid_0: Tools.ShippingChildInv.ChildBnd mref cref w ∧
  Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref `Sparkle.IP.Net.HTTP.httpGetByte
    Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape
```
