import Tests.Compiler.NoPortsMemOnlyAtLib
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `mixedMems` under `MachineClosesAt`: the depth-0 endpoint of a MEMORY-ONLY parent with BOTH read kinds, without the four check premises (G1, unit U4, round par/b-15)

`mixedMems` (`Tests/Compiler/ShippingMachineMemLinkedTest.lean` 38–46, READ):
a `Signal.loop` parent with two register slots, a combinational-read memory
and a synchronous-read memory. MEASURED by the data probe (run
20261013-055644-b13b-alltests): nDecl=3, binders=12, call entries
[SparkleMem.combo.4.8, SparkleMem.sync.4.8], argument lets
[[1, 2, 3, 0], [1, 4, 3, 0]], instFields=[out, out], slots=2, lets=5, loops=1.

## `MemOnlyData` applies AS BUILT — no generalisation is needed

The two memories differ in the READ KIND only; both are aw 4, dw 8.
`MemOnlyData d nDecl aw dw` (`Tools/ShippingMemOnly.lean` 115–132) fixes ONE
`(aw, dw)` and asks the kind entry by entry (`mem : ∀ k hk, ∃ cb, memChild?
… = some (memModule cb aw dw)`); `memOuts dw` / `memIns aw dw` do not depend
on the kind. So `MemOnlyData mixedMems.machineData 3 4 8` is the statement,
with `mem` proved by the two-way `mixedMems_entry`. A per-entry
generalisation (`aw k`, `dw k`) would be needed only for a parent whose
memories differ in a WIDTH; none of the five does, and none is written.

First use of a parent with both kinds in this chain: every data condition
below is a named kernel `decide` (`mixedMems_callArgs` in particular: the
second memory's write data is `Signal.snd st`, argument lets `[1, 4, 3, 0]`);
if one is false the build names it.

## EXPECTED (stated before the build; the audit THROWS otherwise)

BASE: `mixedMems.machine_design_sv0` (there is no `mixedMems.machine_design_svR0`).
The endpoint is a NEW statement, not the base with premises removed
(`Tests/Compiler/NoPortsMemOnlyAtLib.lean`, differences 1–5).

| endpoint | premise | predicted state |
|---|---|---|
| `mixedMems.machine_design_noPortsR0` | `shipsHierCheck (childMap D.modules) b` (of the base) | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` (of the base) | predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` (of the base) | predicted absent, pending build |
| | the base's boundary `True` | REPLACED by `ChildBnd mref cref w` — ADDED antecedent (allowed by the classifier) |
| | the base's `MachineCloses mixedMems` (all worlds, every logger) | REPLACED by `MachineClosesAt mixedMems` — STILL A PREMISE, the one premise NOT ALLOWED; no closed form |
| | `hr`, `MachineDefines mixedMems` | stay |

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
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems 3
    [Sparkle.Compiler.MachMemory.memChildName true 4 8, Sparkle.Compiler.MachMemory.memChildName false 4 8]

namespace Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest
open Tools.ShippingMemKid (memOuts memIns)

/-- The combinational placeholder's child is the built module (the
generators' own `rfl`, `Tools/ShippingMachineMemCommand.lean` 46). -/
theorem mem_isMemC : Sparkle.Compiler.MachMemory.memChild?
    (Sparkle.Compiler.MachMemory.memChildName true 4 8) =
      some (Sparkle.Compiler.MachMemory.memModule true 4 8) := by
  first | rfl | decide

/-- The synchronous placeholder's child is the built module. -/
theorem mem_isMemS : Sparkle.Compiler.MachMemory.memChild?
    (Sparkle.Compiler.MachMemory.memChildName false 4 8) =
      some (Sparkle.Compiler.MachMemory.memModule false 4 8) := by
  first | rfl | decide

/-- Every call entry of `mixedMems` is of ONE OF THE TWO memory placeholders
— the combinational or the synchronous read at aw 4, dw 8 (decided on the
reflected data; no order, no count). -/
theorem mixedMems_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).1 =
        Sparkle.Compiler.MachMemory.memChildName true 4 8 ∨
      ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).1 =
        Sparkle.Compiler.MachMemory.memChildName false 4 8 := by
  first | decide | decide +kernel

theorem mixedMems_calls :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).callsOk 3 =
      true := by
  first | decide | decide +kernel

theorem mixedMems_slots :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).ss.length =
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.layout.slots.length := by
  first | decide | decide +kernel

theorem mixedMems_domB :
    ∀ b ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.binders.drop 3,
      b.2 ≠ .domain := by
  first | decide | decide +kernel

theorem mixedMems_outTy :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem mixedMems_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData 3
    (fun _ => memOuts 8) = true := by
  first | decide | decide +kernel

theorem mixedMems_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData 3
    (fun _ => memIns 4 8) = true := by
  first | decide | decide +kernel

theorem mixedMems_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem mixedMems_outScalar :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- **The data conditions of `mixedMems`** (every field decided above or a
generated constant of the declaration). -/
theorem mixedMems_data : Tools.ShippingMemOnly.MemOnlyData
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData 3 4 8 :=
  Tools.ShippingMemOnly.MemOnlyData.mk
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_body
    mixedMems_calls mixedMems_slots mixedMems_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    mixedMems_outTy
    (fun k hk => (mixedMems_entry k hk).elim
      (fun h => Exists.intro true
        ((congrArg Sparkle.Compiler.MachMemory.memChild? h).trans mem_isMemC))
      (fun h => Exists.intro false
        ((congrArg Sparkle.Compiler.MachMemory.memChild? h).trans mem_isMemS)))
    mixedMems_callWidths mixedMems_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mixedMems_outChars o ho))
    mixedMems_outScalar
    -- origin dispatch: names say what their origins build
    (by first | decide | decide +kernel)

/-- **The run's facts of `mixedMems`'s full-entry module** (`memOnly_runFacts`). -/
theorem mixedMems_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemOnly.memOnly_runFacts mixedMems_data hB hcore hpost entry closes

/-- **The output check at depth 0 under the statement-kind gate**
(`memOnly_outsCheck`). -/
theorem mixedMems_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_outsCheck mixedMems_data hB hcore hpost entry closes hg

/-- **The children's bound of the memory route, `kidsMem`** (`memOnly_kidsMem`):
every instance's child is the built memory module, no connection names its
read latch. -/
theorem mixedMems_kidsMemG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemOnly.memOnly_kidsMem mixedMems_data hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`memOnly_designCheck`). -/
theorem mixedMems_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_designCheck mixedMems_data hB hcore hpost entry closes

end Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
  let name ← Tests.Compiler.NoPortsMemOnlyAt.generateAt f
    ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_runFacts
    ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_outsG0
    ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_kidsMemG
    ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_designP0
  Lean.logInfo m!"NOPORTS MEMONLY AT [{name}]: the depth-0 endpoint of a MEMORY-ONLY parent under MachineClosesAt and ChildBnd, without the shipsHierCheck, designCheck (portsMatchB, kidsPass), outsCheck and kidsMem antecedents of {f}.machine_design_sv0 — a NEW statement (its closing premise is the at-form, its boundary ChildBnd is added); MachineClosesAt is STILL a binder, no closing is proved"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyAt.auditAt
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
    [``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_entry,
     ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_data,
     ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_runFacts,
     ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_outsG0,
     ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_kidsMemG,
     ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_designP0]
