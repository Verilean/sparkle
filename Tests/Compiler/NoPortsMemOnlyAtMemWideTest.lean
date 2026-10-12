import Tests.Compiler.NoPortsMemOnlyAtLib

/-! # `memWide` under `MachineClosesAt`: the depth-0 endpoint of a MEMORY-ONLY parent without the four check premises (G1, unit U4, round par/b-15)

`memWide` (`Tests/Compiler/ShippingDesignSVMemTest.lean` 23–30, READ): a
`Signal.loop` parent with two register slots and ONE combinational-read
memory of OTHER widths, aw 6, dw 16. MEASURED by the data probe (run
20261013-055644-b13b-alltests): nDecl=3, binders=10, call entries
[SparkleMem.combo.6.16], argument lets [[1, 2, 3, 0]], instFields=[out],
slots=2, lets=4, loops=1.

One memory, so `MemOnlyData memWide.machineData 3 6 16` as BUILT applies
(`Tools/ShippingMemOnly.lean` 115–132); the tables are `memOuts 16`,
`memIns 6 16`. NEVER instantiated before at these widths: every data
condition below is a named kernel `decide`; if one is false the build names
it. The theorems are instances of the general `memOnly_*` (one application
each), the pattern of `NoPortsMemOnlyCounterTest`.

## EXPECTED (stated before the build; the audit THROWS otherwise)

BASE: `memWide.machine_design_sv0` (there is no `memWide.machine_design_svR0`).
The endpoint is a NEW statement, not the base with premises removed
(`Tests/Compiler/NoPortsMemOnlyAtLib.lean`, differences 1–5).

| endpoint | premise | predicted state |
|---|---|---|
| `memWide.machine_design_noPortsR0` | `shipsHierCheck (childMap D.modules) b` (of the base) | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` (of the base) | predicted absent, pending build |
| | the base's boundary `True` | REPLACED by `ChildBnd mref cref w` — ADDED antecedent (allowed by the classifier) |
| | the base's `MachineCloses memWide` (all worlds, every logger) | REPLACED by `MachineClosesAt memWide` — STILL A PREMISE, the one premise NOT ALLOWED; no closed form |
| | `hr`, `MachineDefines memWide` | stay |

SCOPE: one declaration, depth 0, data conditions decided per declaration
(`MemOnlyData`: conditions, not reductions), compiler guards with fallback,
`DesignSV` of the module list — not the SV string, not `#sim`. The run, the
reflection, `ChildBnd` and `MachineClosesAt` stay premises. The closing is
NOT worked on here.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyAt.logData
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide 3
    [Sparkle.Compiler.MachMemory.memChildName true 6 16]

namespace Tests.Compiler.NoPortsMemOnlyAtMemWideTest
open Tools.ShippingMemKid (memOuts memIns)

/-- The placeholder's child is the built module (the generators' own `rfl`,
`Tools/ShippingMachineMemCommand.lean` 46). -/
theorem mem_isMem : Sparkle.Compiler.MachMemory.memChild?
    (Sparkle.Compiler.MachMemory.memChildName true 6 16) =
      some (Sparkle.Compiler.MachMemory.memModule true 6 16) := by
  first | rfl | decide

/-- Every call entry of `memWide` is of the memory placeholder (decided on
the reflected data; no order, no count). -/
theorem memWide_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName true 6 16 := by
  first | decide | decide +kernel

theorem memWide_calls :
    (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).callsOk 3 =
      true := by
  first | decide | decide +kernel

theorem memWide_slots :
    (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).ss.length =
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.layout.slots.length := by
  first | decide | decide +kernel

theorem memWide_domB :
    ∀ b ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.binders.drop 3,
      b.2 ≠ .domain := by
  first | decide | decide +kernel

theorem memWide_outTy :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem memWide_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData 3
    (fun _ => memOuts 16) = true := by
  first | decide | decide +kernel

theorem memWide_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData 3
    (fun _ => memIns 6 16) = true := by
  first | decide | decide +kernel

theorem memWide_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem memWide_outScalar :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- **The data conditions of `memWide`** (every field decided above or a
generated constant of the declaration). -/
theorem memWide_data : Tools.ShippingMemOnly.MemOnlyData
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData 3 6 16 :=
  Tools.ShippingMemOnly.MemOnlyData.mk
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_body
    memWide_calls memWide_slots memWide_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    memWide_outTy
    (fun k hk => Exists.intro true
      ((congrArg Sparkle.Compiler.MachMemory.memChild? (memWide_entry k hk)).trans mem_isMem))
    memWide_callWidths memWide_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (memWide_outChars o ho))
    memWide_outScalar

/-- **The run's facts of `memWide`'s full-entry module** (`memOnly_runFacts`). -/
theorem memWide_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemOnly.memOnly_runFacts memWide_data hB hcore hpost entry closes

/-- **The output check at depth 0 under the statement-kind gate**
(`memOnly_outsCheck`). -/
theorem memWide_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_outsCheck memWide_data hB hcore hpost entry closes hg

/-- **The children's bound of the memory route, `kidsMem`** (`memOnly_kidsMem`):
every instance's child is the built memory module, no connection names its
read latch. -/
theorem memWide_kidsMemG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemOnly.memOnly_kidsMem memWide_data hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`memOnly_designCheck`). -/
theorem memWide_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_designCheck memWide_data hB hcore hpost entry closes

end Tests.Compiler.NoPortsMemOnlyAtMemWideTest

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
  let name ← Tests.Compiler.NoPortsMemOnlyAt.generateAt f
    ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_runFacts
    ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_outsG0
    ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_kidsMemG
    ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_designP0
  Lean.logInfo m!"NOPORTS MEMONLY AT [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent under MachineClosesAt and ChildBnd, without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents of {f}.machine_design_sv0 — a NEW statement (its closing premise is the at-form, its boundary ChildBnd is added); MachineClosesAt is STILL a binder, no closing is proved"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyAt.auditAt
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
    [``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_entry,
     ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_data,
     ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_runFacts,
     ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_outsG0,
     ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_designP0]
