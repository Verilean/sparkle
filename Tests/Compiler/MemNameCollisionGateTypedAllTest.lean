import Tests.Compiler.MemNameCollisionGateTypedTest
import Tools.ShippingGateTypedCommand

/-! # The typed design endpoints of the other three gate-collision parents (round par/tgen)

BUILT as written: tg2 (`lake build Tests.Compiler.MemNameCollisionGateTypedAllTest`, exit 0; audits and asserting shadow passed).

`collMixSame_designClosedT` (`MemNameCollisionGateTypedTest`) for the remaining parents of
`Tests/Compiler/MemNameCollisionGateCertTest.lean`, by the GENERATOR
`Tools.ShippingGateTypedCommand.generate` (`addTyped`, parameterized; head
`Tools.ShippingNoPortsTyped.machine_design_noPortsT`):

| parent | memory entry | gate entry (origin `.ord`) | gate value | value equation | result width | argument lets |
|---|---|---|---|---|---|---|
| `collMixDiff` | `.mem true 4 8` (named `comboName`) | `syncName` | `fakeSrc.gateValue` | `syncGate_value` | 8 | equal |
| `collMixArgs` | `.mem false 4 8` (named `syncName`) | `syncName` | `fakeSrc.gateValue` | `syncGate_value` | 8 | different |
| `collWidth` | `.mem true 4 8` (named `comboName`) | `comboName` | `fakeN.gateValue` | `comboGate_value` | 4 | equal |

Per parent: `#machine_endpoint`, `#machine_design_svRG0` (which also generates
`machine_composedTRGA` and `machine_ships_hierRG`; the non-`A` `#machine_composedTRG` is not
needed here), then the lemmas as for `collMixSame` (`_closesR`, `_entry`, `_kids`, `_callWidths`,
`_callArgs`, `_outChars`, `_runFacts`, `_outsG0`, `_designP0`, `_kidTyped`, `_typedRun`) and the
generator. `collMixArgs` goes through the command `#gate_design_typed`, the other two through
the MetaM function.

DIFFERENCE from `collMixSame`: `_entry` states `origin = .mem cb 4 8 ∨ (origin = .ord ∧ name =
cName)` (the memory entry's NAME is not stated: for `collMixDiff` it is `comboName`, not the
gate child's `syncName`); `collMixSame_entry` stated `name = syncName ∧ (… ∨ …)`.

GLOBAL NAMES this module adds outside its namespace (generated, unavoidable with the commands):
`Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.{collMixDiff,collMixArgs,collWidth}.*`
(endpoint data and theorems) and, for `collWidth`'s gate child, `SparkleMem.combo.4.8.*`
(`machineSource`, `machineData`, … from `generateSourceDefs`, and `gate_kid_run`) plus
`Tools.ShippingMachineGateMemCommand.gateKidAux.<hash>`. No other module declares them at
e2618ff8 (checked by grep); a joint-import probe is still needed. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemKid (KidFactsTC memOuts memIns gateOuts gateIns)

-- (writing-time guess, accepted by build tg2): the endpoints of these three parents were never generated before (collMixSame's
-- were, GateDesignTest); the reader data is asserted in GateCertTest (nDecl 3, two entries)
#machine_endpoint Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff
#machine_endpoint Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs
#machine_endpoint Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth

#machine_design_svRG0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff
#machine_design_svRG0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs
-- `prepareGateKids` generates `SparkleMem.combo.4.8.gate_kid_run` here (first use of that child)
-- (writing-time guess, accepted by build tg2): `gateKidTheorem SparkleMem.combo.4.8` (generateSourceDefs + gateDefs on the copy of
-- `fakeN`) is exercised for the first time here; `syncName`'s was built in GateDesignTest
#machine_design_svRG0 Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth

/-- `fakeN`'s outputs / argument widths, keyed by the entry's ORIGIN (as `outsG` / `insG` for
`fakeSrc`). -/
noncomputable def outsFN : InstOrigin → List Sparkle.IR.Machine.OutField
  | .mem _ _ dw => memOuts dw
  | .ord => gateOuts fakeN.gateSort.width
  | .field _ => gateOuts fakeN.gateSort.width

noncomputable def insFN : InstOrigin → List Nat
  | .mem _ aw dw => memIns aw dw
  | .ord => gateIns fakeN.gateBinders
  | .field _ => gateIns fakeN.gateBinders

/-- `fakeN`'s result is 4 bits wide (≠ 1). -/
theorem fakeN_width : fakeN.gateSort.width ≠ 1 := by
  first | decide | decide +kernel

/-! ## `collMixDiff` -/

set_option maxHeartbeats 4000000 in
/-- `collMixDiff_closes` at the endpoint's data constant (the same reader data). -/
theorem collMixDiff_closesR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixDiff
      (collMixDiff.machineData).shape :=
  collMixDiff_closes hR0

/-- Every entry is the `.mem true 4 8` memory or the `.ord` call of `syncName` (decided). -/
theorem collMixDiff_entry : ∀ (k : Nat) (hk : k < (collMixDiff.machineData).shape.insts.length),
    originAt (collMixDiff.machineData).shape k = .mem true 4 8 ∨
      (originAt (collMixDiff.machineData).shape k = .ord ∧
        ((collMixDiff.machineData).shape.insts[k]).1 = syncName) := by
  -- (writing-time guess, accepted by build tg2): the reshaped statement (memory name not stated) decides as collMixSame_entry did
  first | decide | decide +kernel

/-- **`KidFactsTC` of every call entry of `collMixDiff`, by ORIGIN**, at depth 0. -/
theorem collMixDiff_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixDiff.machineData).shape.insts.length),
      KidFactsTC mref cref (originAt (collMixDiff.machineData).shape k)
        ((collMixDiff.machineData).shape.insts[k]).1
        (outsG (originAt (collMixDiff.machineData).shape k))
        (insG (originAt (collMixDiff.machineData).shape k)) 0 := by
  intro k hk
  rcases collMixDiff_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho]
    exact (Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem true 4 8)).toC
  · rw [ho, hn]
    exact Tools.ShippingMemKid.gateKidT_factsC (o := InstOrigin.ord) (c := syncName)
      (bs := fakeSrc.gateBinders) rfl hR0
      fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width 0

theorem collMixDiff_callWidths : Tools.ShippingCallWidths.callWidthsOk collMixDiff.machineData 3
    (fun k => outsG (originAt (collMixDiff.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixDiff_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk collMixDiff.machineData 3
    (fun k => insG (originAt (collMixDiff.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixDiff_outChars :
    ∀ o ∈ (collMixDiff.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `collMixDiff`'s full-entry module** (`kidsC_runFactsT`). -/
theorem collMixDiff_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixDiff [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixDiff
      (collMixDiff.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemKid.kidsC_runFactsT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixDiff.machineData).shape k))
    (fun k => insG (originAt (collMixDiff.machineData).shape k)) 0
    (collMixDiff_kids hR0) collMixDiff_callWidths
    hB hcore hpost entry (collMixDiff_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 0 under the statement-kind gate** (`kidsC_outsCheckT`). -/
theorem collMixDiff_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixDiff [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixDiff
      (collMixDiff.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_outsCheckT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixDiff.machineData).shape k))
    (fun k => insG (originAt (collMixDiff.machineData).shape k)) 0
    (collMixDiff_kids hR0)
    hB hcore hpost entry (collMixDiff_closesR hR0) hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsC_designCheckT`). -/
theorem collMixDiff_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixDiff [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixDiff
      (collMixDiff.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_designCheckT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixDiff.machineData).shape k))
    (fun k => insG (originAt (collMixDiff.machineData).shape k)) 0
    (collMixDiff_kids hR0) collMixDiff_callWidths collMixDiff_callArgs
    hB hcore hpost entry (collMixDiff_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixDiff_outChars o ho))
    (by first | decide | decide +kernel)

/-- Per kid, by origin: the memory entry is `FlatOk`, the `.ord` entry (the gate child) is
`KidTyped`. -/
theorem collMixDiff_kidTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixDiff.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixDiff.machineData).shape k)
        ((collMixDiff.machineData).shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  intro k hk y hy
  rcases collMixDiff_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem true 4 8)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (Tools.ShippingKidsTyped.kidTyped_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl)))

set_option maxHeartbeats 4000000 in
/-- **The typed children bound of `collMixDiff`'s full-entry module** (`core_typedRunMT`). -/
theorem collMixDiff_typedRun {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixDiff [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixDiff
      (collMixDiff.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsTyped.TypedRun (Tools.ShippingMachineLinked.childMap D.modules) b
      Tools.ShippingMachineShipsHier.mixInv :=
  Tools.ShippingKidsTyped.core_typedRunMT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixDiff.machineData).shape k))
    (fun k => insG (originAt (collMixDiff.machineData).shape k)) 0
    (collMixDiff_kids hR0) collMixDiff_callArgs (collMixDiff_kidTyped hR0)
    hB hcore hpost entry (collMixDiff_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixDiff_outChars o ho))
    (by first | decide | decide +kernel)

/-! ## `collMixArgs` -/

set_option maxHeartbeats 4000000 in
/-- `collMixArgs_closes` at the endpoint's data constant (the same reader data). -/
theorem collMixArgs_closesR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collMixArgs
      (collMixArgs.machineData).shape :=
  collMixArgs_closes hR0

/-- Every entry is the `.mem false 4 8` memory or the `.ord` call of `syncName` (decided). -/
theorem collMixArgs_entry : ∀ (k : Nat) (hk : k < (collMixArgs.machineData).shape.insts.length),
    originAt (collMixArgs.machineData).shape k = .mem false 4 8 ∨
      (originAt (collMixArgs.machineData).shape k = .ord ∧
        ((collMixArgs.machineData).shape.insts[k]).1 = syncName) := by
  first | decide | decide +kernel

/-- **`KidFactsTC` of every call entry of `collMixArgs`, by ORIGIN**, at depth 0. -/
theorem collMixArgs_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixArgs.machineData).shape.insts.length),
      KidFactsTC mref cref (originAt (collMixArgs.machineData).shape k)
        ((collMixArgs.machineData).shape.insts[k]).1
        (outsG (originAt (collMixArgs.machineData).shape k))
        (insG (originAt (collMixArgs.machineData).shape k)) 0 := by
  intro k hk
  rcases collMixArgs_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho]
    exact (Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem false 4 8)).toC
  · rw [ho, hn]
    exact Tools.ShippingMemKid.gateKidT_factsC (o := InstOrigin.ord) (c := syncName)
      (bs := fakeSrc.gateBinders) rfl hR0
      fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) fakeSrc_width 0

theorem collMixArgs_callWidths : Tools.ShippingCallWidths.callWidthsOk collMixArgs.machineData 3
    (fun k => outsG (originAt (collMixArgs.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixArgs_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk collMixArgs.machineData 3
    (fun k => insG (originAt (collMixArgs.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collMixArgs_outChars :
    ∀ o ∈ (collMixArgs.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `collMixArgs`'s full-entry module** (`kidsC_runFactsT`). -/
theorem collMixArgs_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixArgs [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixArgs
      (collMixArgs.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemKid.kidsC_runFactsT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixArgs.machineData).shape k))
    (fun k => insG (originAt (collMixArgs.machineData).shape k)) 0
    (collMixArgs_kids hR0) collMixArgs_callWidths
    hB hcore hpost entry (collMixArgs_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 0 under the statement-kind gate** (`kidsC_outsCheckT`). -/
theorem collMixArgs_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixArgs [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixArgs
      (collMixArgs.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_outsCheckT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixArgs.machineData).shape k))
    (fun k => insG (originAt (collMixArgs.machineData).shape k)) 0
    (collMixArgs_kids hR0)
    hB hcore hpost entry (collMixArgs_closesR hR0) hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsC_designCheckT`). -/
theorem collMixArgs_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixArgs [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixArgs
      (collMixArgs.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_designCheckT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixArgs.machineData).shape k))
    (fun k => insG (originAt (collMixArgs.machineData).shape k)) 0
    (collMixArgs_kids hR0) collMixArgs_callWidths collMixArgs_callArgs
    hB hcore hpost entry (collMixArgs_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixArgs_outChars o ho))
    (by first | decide | decide +kernel)

/-- Per kid, by origin: the memory entry is `FlatOk`, the `.ord` entry (the gate child) is
`KidTyped`. -/
theorem collMixArgs_kidTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixArgs.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixArgs.machineData).shape k)
        ((collMixArgs.machineData).shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  intro k hk y hy
  rcases collMixArgs_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem false 4 8)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (Tools.ShippingKidsTyped.kidTyped_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl)))

set_option maxHeartbeats 4000000 in
/-- **The typed children bound of `collMixArgs`'s full-entry module** (`core_typedRunMT`). -/
theorem collMixArgs_typedRun {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixArgs [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixArgs
      (collMixArgs.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsTyped.TypedRun (Tools.ShippingMachineLinked.childMap D.modules) b
      Tools.ShippingMachineShipsHier.mixInv :=
  Tools.ShippingKidsTyped.core_typedRunMT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsG (originAt (collMixArgs.machineData).shape k))
    (fun k => insG (originAt (collMixArgs.machineData).shape k)) 0
    (collMixArgs_kids hR0) collMixArgs_callArgs (collMixArgs_kidTyped hR0)
    hB hcore hpost entry (collMixArgs_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixArgs_outChars o ho))
    (by first | decide | decide +kernel)

/-! ## `collWidth` -/

set_option maxHeartbeats 4000000 in
/-- `collWidth_closes` at the endpoint's data constant (the same reader data). -/
theorem collWidth_closesR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collWidth
      (collWidth.machineData).shape :=
  collWidth_closes hR0

/-- Every entry is the `.mem true 4 8` memory or the `.ord` call of `comboName` (decided). -/
theorem collWidth_entry : ∀ (k : Nat) (hk : k < (collWidth.machineData).shape.insts.length),
    originAt (collWidth.machineData).shape k = .mem true 4 8 ∨
      (originAt (collWidth.machineData).shape k = .ord ∧
        ((collWidth.machineData).shape.insts[k]).1 = comboName) := by
  first | decide | decide +kernel

/-- **`KidFactsTC` of every call entry of `collWidth`, by ORIGIN**, at depth 0. -/
theorem collWidth_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    ∀ (k : Nat) (hk : k < (collWidth.machineData).shape.insts.length),
      KidFactsTC mref cref (originAt (collWidth.machineData).shape k)
        ((collWidth.machineData).shape.insts[k]).1
        (outsFN (originAt (collWidth.machineData).shape k))
        (insFN (originAt (collWidth.machineData).shape k)) 0 := by
  intro k hk
  rcases collWidth_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho]
    exact (Tools.ShippingMemKid.memKidT_facts (Tools.ShippingInstTagged.child?_mem true 4 8)).toC
  · rw [ho, hn]
    exact Tools.ShippingMemKid.gateKidT_factsC (o := InstOrigin.ord) (c := comboName)
      (bs := fakeN.gateBinders) rfl hR0
      fakeN.gate_old fakeN.gate_peel fakeN.gate_wf
      (Tools.ShippingGateChild.bool_positions (by decide))
      (Tools.ShippingGateChild.bits_positions (by decide)) fakeN_width 0

theorem collWidth_callWidths : Tools.ShippingCallWidths.callWidthsOk collWidth.machineData 3
    (fun k => outsFN (originAt (collWidth.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collWidth_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk collWidth.machineData 3
    (fun k => insFN (originAt (collWidth.machineData).shape k)) = true := by
  first | decide | decide +kernel

theorem collWidth_outChars :
    ∀ o ∈ (collWidth.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `collWidth`'s full-entry module** (`kidsC_runFactsT`). -/
theorem collWidth_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collWidth [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collWidth
      (collWidth.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemKid.kidsC_runFactsT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsFN (originAt (collWidth.machineData).shape k))
    (fun k => insFN (originAt (collWidth.machineData).shape k)) 0
    (collWidth_kids hR0) collWidth_callWidths
    hB hcore hpost entry (collWidth_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 0 under the statement-kind gate** (`kidsC_outsCheckT`). -/
theorem collWidth_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collWidth [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collWidth
      (collWidth.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_outsCheckT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsFN (originAt (collWidth.machineData).shape k))
    (fun k => insFN (originAt (collWidth.machineData).shape k)) 0
    (collWidth_kids hR0)
    hB hcore hpost entry (collWidth_closesR hR0) hg

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsC_designCheckT`). -/
theorem collWidth_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collWidth [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collWidth
      (collWidth.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemKid.kidsC_designCheckT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsFN (originAt (collWidth.machineData).shape k))
    (fun k => insFN (originAt (collWidth.machineData).shape k)) 0
    (collWidth_kids hR0) collWidth_callWidths collWidth_callArgs
    hB hcore hpost entry (collWidth_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collWidth_outChars o ho))
    (by first | decide | decide +kernel)

/-- Per kid, by origin: the memory entry is `FlatOk`, the `.ord` entry (the gate child) is
`KidTyped`. -/
theorem collWidth_kidTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    ∀ (k : Nat) (hk : k < (collWidth.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collWidth.machineData).shape k)
        ((collWidth.machineData).shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ Tools.ShippingKidsTyped.KidTyped y.1 := by
  intro k hk y hy
  rcases collWidth_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    exact Or.inl ((Tools.ShippingMemKid.memKidT_facts
      (Tools.ShippingInstTagged.child?_mem true 4 8)).flat y hy)
  · rw [ho, hn] at hy
    exact Or.inr (Tools.ShippingKidsTyped.kidTyped_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeN.gateBinders) hR0
        fakeN.gate_old fakeN.gate_peel fakeN.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl)))

set_option maxHeartbeats 4000000 in
/-- **The typed children bound of `collWidth`'s full-entry module** (`core_typedRunMT`). -/
theorem collWidth_typedRun {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collWidth [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collWidth
      (collWidth.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingKidsTyped.TypedRun (Tools.ShippingMachineLinked.childMap D.modules) b
      Tools.ShippingMachineShipsHier.mixInv :=
  Tools.ShippingKidsTyped.core_typedRunMT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun k => outsFN (originAt (collWidth.machineData).shape k))
    (fun k => insFN (originAt (collWidth.machineData).shape k)) 0
    (collWidth_kids hR0) collWidth_callArgs (collWidth_kidTyped hR0)
    hB hcore hpost entry (collWidth_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collWidth_outChars o ho))
    (by first | decide | decide +kernel)

/-! ## The endpoints, by the generator (MetaM / command; the kernel checks the results) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  for (p, cC, src, eqN) in [(`collMixDiff, `syncName, `fakeSrc, `syncGate_value),
      (`collWidth, `comboName, `fakeN, `comboGate_value)] do
    let n ← Tools.ShippingGateTypedCommand.generateTop
      { parent := ns ++ p, name := tn ++ p.appendAfter "_designClosedT",
        childConst := ns ++ cC, gateValue := ns ++ src ++ `gateValue,
        valueEq? := some (ns ++ eqN),
        runFacts := tn ++ p.appendAfter "_runFacts", outsG0 := tn ++ p.appendAfter "_outsG0",
        typedRun := tn ++ p.appendAfter "_typedRun", designP0 := tn ++ p.appendAfter "_designP0",
        closesR := tn ++ p.appendAfter "_closesR" }
    Lean.logInfo m!"GATETYPEDALL [{n}]: shipsHierCheck, designCheck, outsCheck discharged; the children bound TYPED (core_typedRunMT: memory FlatOk, gate KidTyped); MachineClosesAt by {p}_closesR; the boundary's reflection merged with hR0 by {eqN}; ADDED run hypothesis of the conclusion: BoundOff (declWidth b) outputs st0"

-- the command form (writing-time guess accepted by build tg2: its syntax is new; the MetaM form above is the fallback)
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#gate_design_typed Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs
  collMixArgs_designClosedT
  Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
  Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue
  collMixArgs_runFacts collMixArgs_outsG0 collMixArgs_typedRun collMixArgs_designP0
  collMixArgs_closesR
  value_eq Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncGate_value

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let bindersOf (t : Lean.Expr) : Lean.MetaM (Array String) :=
    Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
  let inner (t : Lean.Expr) := Lean.Meta.forallTelescope t fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  for p in [`collMixDiff, `collMixArgs, `collWidth] do
    let fin := tn ++ p.appendAfter "_designClosedT"
    -- (a) standard axioms
    for n in [``Tools.ShippingNoPortsTyped.machine_design_noPortsT,
        ns ++ p ++ `machine_ships_hierRG, ns ++ p ++ `machine_design_svRG0,
        tn ++ p.appendAfter "_closesR", tn ++ p.appendAfter "_kids",
        tn ++ p.appendAfter "_runFacts", tn ++ p.appendAfter "_outsG0",
        tn ++ p.appendAfter "_designP0", tn ++ p.appendAfter "_kidTyped",
        tn ++ p.appendAfter "_typedRun", fin] do
      unless (← Lean.getEnv).contains n do throwError "{n}: missing"
      Tests.Compiler.NoPortsTest.stdAxioms n
    -- (b) the final statement: no checker, no children bound (old or new), no closing,
    -- no TagsAgree
    let finT := (← Lean.getConstInfo fin).type
    for k in Tests.Compiler.NoPortsTest.checkers ++
        [``Tools.ShippingMachineShipsHier.kidsMem, ``Tools.ShippingMachineShipsHier.kidsMasked,
         ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingKidsMixedC.kidsMixedC,
         ``Tools.ShippingKidsMixedC.combAt, ``Tools.ShippingKidsMixedC.combOk,
         ``Tools.ShippingKidsMixedC.combChain,
         ``Tools.ShippingKidsTyped.TypedRun, ``Tools.ShippingKidsTyped.KidTyped,
         ``Tools.ShippingInstTagged.TagsAgree, ``Tools.ShippingInstTagged.tagAgrees,
         ``Tools.ShippingChildInv.MachineClosesAt] do
      if (finT.find? (·.isConstOf k)).isSome then
        throwError "{fin}: the statement mentions {k}"
    -- the added run hypothesis of the conclusion is there (reported, not hidden)
    unless (finT.find? (·.isConstOf ``Tools.ShippingHierTyped.BoundOff)).isSome do
      throwError "{fin}: does not mention BoundOff (the report says the initial-state condition was added)"
    -- (c) the Prop binders and the antecedents under the existentials, LOGGED
    let bs ← bindersOf finT
    let ia ← inner finT
    Lean.logInfo m!"GATETYPEDALL PREMISES {fin}: {bs.size} Prop binders {bs}; {ia.size} antecedents under the existentials {ia.map (·.1)}"
    unless bs.size == 3 do
      throwError "{fin}: {bs.size} Prop binders, expected 3 (the run, MachineDefines, EntryDefines)"
    unless ia.size == 1 do
      throwError "{fin}: {ia.size} antecedents under the existentials, expected 1 (ChildBnd): {ia.map (·.1)}"
    -- the three binders are the run, `MachineDefines` and `EntryDefines`; the antecedent `ChildBnd`
    let kinds ← Lean.Meta.forallTelescope finT fun xs _ => do
      let mut out : Array Lean.Name := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (ty.getAppFn.constName?.getD .anonymous)
      return out
    unless kinds == #[``Tools.ShippingEntrySoundness.RunsTo,
        ``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingInlineSoundness.EntryDefines] do
      throwError "{fin}: the Prop binders' heads are {kinds}"
    unless (ia[0]!.1.splitOn "ChildBnd").length > 1 do
      throwError "{fin}: the antecedent is not ChildBnd: {ia[0]!.1}"
    -- exactly ONE reflection (`EntryDefines`) in the whole statement: the merged binder
    let cnt := Tools.ShippingGateTypedCommand.countApps
      ``Tools.ShippingInlineSoundness.EntryDefines 6 finT
    unless cnt == 1 do
      throwError "{fin}: {cnt} EntryDefines occurrences, expected 1"
    Lean.logInfo m!"GATETYPEDALL {fin}: EntryDefines occurrences {cnt}; no combOk / kidsMixedC / checker in the statement; 3 Prop binders"

#print axioms collMixDiff_designClosedT
#print axioms collMixArgs_designClosedT
#print axioms collWidth_designClosedT

/-! ## Shadow (asserting): the statements are not vacuous on the compiled designs

On the certified compile of each parent (`synthesizeCombinationalCoreWith`, certified front end —
the route of the run, not the run itself): the three-way `kidsMixedC` is TRUE on the top and the
merged bodies, and the colliding gate child's module satisfies `combOk`. `kidsMixed` (the old,
vacuous bound) is LOGGED, not asserted. The shipped module's ports are logged. Shadow evidence
about one compile each, not a proof. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  for (p, cName) in [(ns ++ `collMixDiff, Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName),
      (ns ++ `collMixArgs, Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName),
      (ns ++ `collWidth, Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.comboName)] do
    let (top, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith
      (fun env e h t n => Sparkle.Compiler.Elab.translateExprToWire env e h t n) p [] false
      (certifiedFrontEnd := true)
    let cm := Tools.ShippingMachineLinked.childMap D.modules
    let merged := Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule top)
    let mut old : Array Bool := #[]
    for (lbl, body) in [("top", top.body), ("merged", merged.body)] do
      old := old.push (Tools.ShippingMachineShipsHier.kidsMixed cm body)
      unless Tools.ShippingKidsMixedC.kidsMixedC cm body do
        throwError "{p} ({lbl}): kidsMixedC fails on the compiled design"
    let mn := Sparkle.IR.ModuleName.ofDecl cName
    let some c := D.modules.find? (·.name == mn) | throwError "{p}: no module {mn}"
    unless Tools.ShippingKidsMixedC.combOk c (Sparkle.IR.RegDedup.declWidth c) do
      throwError "{p}: the colliding gate child's module fails combOk"
    let shipped := Sparkle.IR.OptCheck.checkedOptimize merged
    let ports (l : List Sparkle.IR.AST.Port) := l.map fun q => s!"{q.name}:{q.ty.bitWidth}"
    Lean.logInfo m!"GATETYPEDALL SHADOW {p}: kidsMixedC true (top, merged); combOk true on {mn}; kidsMixed (old bound, top/merged) = {old}; modules {D.modules.map (·.name)}; shipped {shipped.name} inputs {ports shipped.inputs} outputs {ports shipped.outputs}"

end Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
