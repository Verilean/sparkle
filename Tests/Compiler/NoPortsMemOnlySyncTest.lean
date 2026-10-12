import Tests.Compiler.NoPortsMemOnlyCounterTest

/-! # `syncNarrow` by hand: the depth-0 endpoint of a MEMORY-ONLY parent with a SYNCHRONOUS-read memory, without the four check premises (G1, unit U4, round par/b-14)

The pattern of `Tests/Compiler/NoPortsMemOnlyCounterTest.lean` (its generator
`generateM0` and audit `auditM0`, its READ / MEASURED notes and its SCOPE) on
`syncNarrow`: a `Signal.loop` parent with ONE synchronous-read memory
(`Signal.memory`, aw 3, dw 5; `Tests/Compiler/ShippingDesignSVMemTest.lean`
33–40; its `…machine_design_sv0` at 58). MEASURED by the probe (run
20261013-055644-b13b-alltests): nDecl=3, binders=10, call entries
[SparkleMem.sync.3.5], argument lets [[1, 2, 3, 0]], instFields=[out],
slots=2, lets=4, loops=1.

READ: `memKid_facts` is stated for both read kinds — `cb` is a variable of it
(`Tools/ShippingMemKidFacts.lean` 468–470), its fields come from the `mem_*`
lemmas over a variable `cb` (192–387) and `leafCheck_memModule cb`
(`Tools/ShippingDesignSVMem.lean` 37, proved by `cases cb`). NOT MEASURED:
this is the first declaration that instantiates `cb = false` in this chain.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `syncNarrow.machine_design_sv0` | predicted state |
|---|---|---|
| `syncNarrow.machine_design_noPorts0` | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` | predicted absent, pending build |
| | the old boundary `True` | REPLACED by `ChildBnd mref cref w` — an antecedent the old endpoint does NOT have |
| | `MachineCloses syncNarrow` (all worlds, every logger) | STILL A PREMISE (a binder), unchanged |
| | `hr`, `MachineDefines syncNarrow` | stay |

SCOPE: one declaration, depth 0, data conditions decided per declaration
(`MemOnlyData`), compiler guards with fallback, `DesignSV` of the module
list — not the SV string, not `#sim`. The run, the reflection, `ChildBnd`
and the all-worlds closing stay premises.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
  let mem := Sparkle.Compiler.MachMemory.memChildName false 3 5
  let rf ← Tools.ShippingMachineCommand.readMachine f
  let fe := rf.shape.insts.map (·.1)
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for s in [`machineData, `machine_ok, `machine_body, `machine_sound, `machine_composedT,
      `machine_closes, `machine_ships_hier, `machine_ships_hierR, `machine_design_sv0,
      `machine_design_svR0, `machine_design_noPorts0] do
    if env.contains (f ++ s) then have_ := have_ ++ [s] else lack := lack ++ [s]
  Lean.logInfo m!"NOPORTS MEMONLY DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {fe}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}, loops={rf.shape.loops.length}; the memory placeholder {mem}; constants present {have_}; absent {lack}"
  unless rf.nDecl == 3 do throwError "{f}: nDecl = {rf.nDecl}, the hand theorems are written for 3"
  if fe.isEmpty then throwError "{f}: no call entry"
  for e in fe do
    unless e == mem do
      throwError "{f}: the call entries are {fe}; {e} is not {mem}"
  if rf.shape.instFields.isEmpty then throwError "{f}: instFields = [] — not the general closing"
  if rf.shape.layout.slots.isEmpty then
    throwError "{f}: NO REGISTER SLOT — the parent-without-a-register axis (hsl : d.shape.layout.slots ≠ [] of kidsM_runFacts / kidsM_designCheck fails); nothing below applies"
  for n in [f ++ `machine_ships_hier, f ++ `machine_design_sv0, f ++ `machineData,
      f ++ `machine_ok, f ++ `machine_body] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_design_noPorts0] do
    if env.contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsMemOnlySyncTest
open Tools.ShippingMemKid (memOuts memIns)

/-- The placeholder's child is the built module (the generators' own `rfl`,
`Tools/ShippingMachineMemCommand.lean` 46). -/
theorem mem_isMem : Sparkle.Compiler.MachMemory.memChild?
    (Sparkle.Compiler.MachMemory.memChildName false 3 5) =
      some (Sparkle.Compiler.MachMemory.memModule false 3 5) := by
  first | rfl | decide

/-- Every call entry of `syncNarrow` is of the memory placeholder (decided on
the reflected data; no order, no count). -/
theorem syncNarrow_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName false 3 5 := by
  first | decide | decide +kernel

theorem syncNarrow_calls :
    (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).callsOk 3 =
      true := by
  first | decide | decide +kernel

theorem syncNarrow_slots :
    (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).ss.length =
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.layout.slots.length := by
  first | decide | decide +kernel

theorem syncNarrow_domB :
    ∀ b ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.binders.drop 3,
      b.2 ≠ .domain := by
  first | decide | decide +kernel

theorem syncNarrow_outTy :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem syncNarrow_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData 3
    (fun _ => memOuts 5) = true := by
  first | decide | decide +kernel

theorem syncNarrow_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData 3
    (fun _ => memIns 3 5) = true := by
  first | decide | decide +kernel

theorem syncNarrow_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem syncNarrow_outScalar :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- **The data conditions of `syncNarrow`** (every field decided above or a
generated constant of the declaration). -/
theorem syncNarrow_data : Tools.ShippingMemOnly.MemOnlyData
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData 3 3 5 :=
  Tools.ShippingMemOnly.MemOnlyData.mk
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_body
    syncNarrow_calls syncNarrow_slots syncNarrow_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    syncNarrow_outTy
    (fun k hk => Exists.intro false
      ((congrArg Sparkle.Compiler.MachMemory.memChild? (syncNarrow_entry k hk)).trans mem_isMem))
    syncNarrow_callWidths syncNarrow_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (syncNarrow_outChars o ho))
    syncNarrow_outScalar

/-- **The run's facts of `syncNarrow`'s full-entry module** (`memOnly_runFacts`). -/
theorem syncNarrow_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemOnly.memOnly_runFacts syncNarrow_data hB hcore hpost entry closes

/-- **The output check at depth 0 under the statement-kind gate**
(`memOnly_outsCheck`). -/
theorem syncNarrow_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_outsCheck syncNarrow_data hB hcore hpost entry closes hg

/-- **The children's bound of the memory route, `kidsMem`** (`memOnly_kidsMem`):
every instance's child is the built memory module, no connection names its
read latch. -/
theorem syncNarrow_kidsMemG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemOnly.memOnly_kidsMem syncNarrow_data hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`memOnly_designCheck`). -/
theorem syncNarrow_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_designCheck syncNarrow_data hB hcore hpost entry closes

end Tests.Compiler.NoPortsMemOnlySyncTest

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemOnly.generateM0 f
      ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_runFacts
      ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_outsG0
      ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_kidsMemG
      ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_designP0
  Lean.logInfo m!"NOPORTS MEMONLY [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents — by hand (syncNarrow_data: MemOnlyData; syncNarrow_runFacts, syncNarrow_outsG0, syncNarrow_kidsMemG, syncNarrow_designP0: Tools.ShippingMemOnly.memOnly_* at depth 0). Its boundary is ChildBnd of the run's start world in place of the old True (ADDED); MachineCloses (all worlds) is STILL a binder"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnly.auditM0
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow
    [``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_entry,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_data,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_runFacts,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_outsG0,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlySyncTest.syncNarrow_designP0]
