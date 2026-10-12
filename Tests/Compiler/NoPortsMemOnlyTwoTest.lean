import Tests.Compiler.NoPortsMemOnlyCounterTest

/-! # `twoMems` by hand: the depth-0 endpoint of a MEMORY-ONLY parent with TWO memory entries, without the four check premises (G1, unit U4, round par/b-14)

The pattern of `Tests/Compiler/NoPortsMemOnlyCounterTest.lean` (its generator
`generateM0` and audit `auditM0`, its READ / MEASURED notes and its SCOPE) on
`twoMems`: a `Signal.loop` parent with TWO combinational-read memories of the
same widths (aw 4, dw 8; `Tests/Compiler/ShippingMachineMemLinkedTest.lean`
26–34; its `…machine_design_sv0` at `ShippingDesignSVMemTest` 51–52).
MEASURED by the probe (run 20261013-055644-b13b-alltests): nDecl=3,
binders=12, call entries [SparkleMem.combo.4.8, SparkleMem.combo.4.8],
argument lets [[1, 2, 3, 0], [0, 2, 3, 4]], instFields=[out, out], slots=2,
lets=5, loops=1.

Two call entries of ONE placeholder name: `twoMems_entry` decides every
entry, and the tables of `MemOnlyData` are constant in the entry
(`fun _ => memOuts 8`, `fun _ => memIns 4 8`). NOT MEASURED: whether the
emitted module has two instances of the one memory module or one (the
general theorems speak of every instance statement, whatever their number).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `twoMems.machine_design_sv0` | predicted state |
|---|---|---|
| `twoMems.machine_design_noPorts0` | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` | predicted absent, pending build |
| | the old boundary `True` | REPLACED by `ChildBnd mref cref w` — an antecedent the old endpoint does NOT have |
| | `MachineCloses twoMems` (all worlds, every logger) | STILL A PREMISE (a binder), unchanged |
| | `hr`, `MachineDefines twoMems` | stay |

SCOPE: one declaration, depth 0, data conditions decided per declaration
(`MemOnlyData`), compiler guards with fallback, `DesignSV` of the module
list — not the SV string, not `#sim`. The run, the reflection, `ChildBnd`
and the all-worlds closing stay premises.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
  let mem := Sparkle.Compiler.MachMemory.memChildName true 4 8
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

namespace Tests.Compiler.NoPortsMemOnlyTwoTest
open Tools.ShippingMemKid (memOuts memIns)

/-- The placeholder's child is the built module (the generators' own `rfl`,
`Tools/ShippingMachineMemCommand.lean` 46). -/
theorem mem_isMem : Sparkle.Compiler.MachMemory.memChild?
    (Sparkle.Compiler.MachMemory.memChildName true 4 8) =
      some (Sparkle.Compiler.MachMemory.memModule true 4 8) := by
  first | rfl | decide

/-- Every call entry of `twoMems` is of the memory placeholder (decided on
the reflected data; no order, no count). -/
theorem twoMems_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName true 4 8 := by
  first | decide | decide +kernel

theorem twoMems_calls :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).callsOk 3 =
      true := by
  first | decide | decide +kernel

theorem twoMems_slots :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).ss.length =
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.layout.slots.length := by
  first | decide | decide +kernel

theorem twoMems_domB :
    ∀ b ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.binders.drop 3,
      b.2 ≠ .domain := by
  first | decide | decide +kernel

theorem twoMems_outTy :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem twoMems_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData 3
    (fun _ => memOuts 8) = true := by
  first | decide | decide +kernel

theorem twoMems_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData 3
    (fun _ => memIns 4 8) = true := by
  first | decide | decide +kernel

theorem twoMems_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem twoMems_outScalar :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- **The data conditions of `twoMems`** (every field decided above or a
generated constant of the declaration). -/
theorem twoMems_data : Tools.ShippingMemOnly.MemOnlyData
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData 3 4 8 :=
  Tools.ShippingMemOnly.MemOnlyData.mk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_body
    twoMems_calls twoMems_slots twoMems_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    twoMems_outTy
    (fun k hk => Exists.intro true
      ((congrArg Sparkle.Compiler.MachMemory.memChild? (twoMems_entry k hk)).trans mem_isMem))
    twoMems_callWidths twoMems_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (twoMems_outChars o ho))
    twoMems_outScalar

/-- **The run's facts of `twoMems`'s full-entry module** (`memOnly_runFacts`). -/
theorem twoMems_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemOnly.memOnly_runFacts twoMems_data hB hcore hpost entry closes

/-- **The output check at depth 0 under the statement-kind gate**
(`memOnly_outsCheck`). -/
theorem twoMems_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_outsCheck twoMems_data hB hcore hpost entry closes hg

/-- **The children's bound of the memory route, `kidsMem`** (`memOnly_kidsMem`):
every instance's child is the built memory module, no connection names its
read latch. -/
theorem twoMems_kidsMemG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemOnly.memOnly_kidsMem twoMems_data hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`memOnly_designCheck`). -/
theorem twoMems_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_designCheck twoMems_data hB hcore hpost entry closes

end Tests.Compiler.NoPortsMemOnlyTwoTest

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemOnly.generateM0 f
      ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_runFacts
      ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_outsG0
      ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_kidsMemG
      ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_designP0
  Lean.logInfo m!"NOPORTS MEMONLY [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents — by hand (twoMems_data: MemOnlyData; twoMems_runFacts, twoMems_outsG0, twoMems_kidsMemG, twoMems_designP0: Tools.ShippingMemOnly.memOnly_* at depth 0). Its boundary is ChildBnd of the run's start world in place of the old True (ADDED); MachineCloses (all worlds) is STILL a binder"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnly.auditM0
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
    [``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_entry,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_data,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_runFacts,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_outsG0,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlyTwoTest.twoMems_designP0]
