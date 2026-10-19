import Tests.Compiler.MemNameCollisionGateBoundTest
import Tests.Compiler.MemNameCollisionKidsSatTest
import Tools.ShippingGateTypedCommandW
import Tools.ShippingSatAssembly
import Tools.ShippingInputWiresRun
-- Round par/sat. BUILT: sa1 (ComposedGW, NoPortsTypedBW exit ok; SatInputs failed: 7 tactic/term errors, fixed by the worker), sa2 (all, exit 0, 669 jobs).
-- `Tests.Compiler.MemNameCollisionKidsSatTest` is the sibling round's file (par/kids,
-- ~/sparkle-work/wt-kids), with `<p>_kidsSat`; it must be merged first.

/-! # The four collision parents: the head's run hypotheses satisfied (round par/sat)

`<p>_designClosedB` (`MemNameCollisionGateBoundTest`) has the run hypotheses (1)-(12) under its
existentials `ids`, `cache`, `regs`, `raw`, `D`; `regs` is opaque there (only `Nodup` and the
length), so hypothesis (2) `∀ t st r, r ∈ regs → seedIn b ins t st r = st r` cannot be discharged
by a user, and nothing pins `raw`, `D` to a run.

Here:

* `<p>.machine_composedTRGAW` and `<p>_designClosedBW`: the same generated chain with the producer
  `machine_linkedT_callsRGW`, `composedGW_of_T` and the head `machine_design_noPortsTBW`
  (`Tools.ShippingGateTypedCommandW.generateTopW`; the kernel checks the results). The conclusion
  additionally exports the core run of `raw`, `D`, `MachineWired` of the same `ids`, `cache`, `regs`,
  and `b.inputs = raw.inputs`.
* run facts of the core run: `<p>_gate` (`core_hierGateMT`), `<p>_oi` (`core_closed_typedInMT`,
  field `oi`), `<p>_inputWires` (`Tools.ShippingInputWiresRun.inputWires_runMT`), `<p>_names`
  (existing), `<p>_kidsSat` (sibling round).
* `<p>_sat`: `Tools.ShippingSatAssembly.sat_of_designClosedBW` at these, built by elaborating one term
  (its statement is the inferred type; the kernel checks it). For EVERY typed input stream and
  EVERY `T`: `ins` (the stream at the declared ports), `st0 = 0`, `kids` (from `<p>_kidsSat`)
  satisfy all twelve run hypotheses, so a closed run of the emitted texts of length `T` exists and
  shows the source, and every such run shows it.

REMAINING premises of `<p>_sat` (the outer premises, unchanged): the full-entry run `hr`,
`MachineDefines` (`entry`), `EntryDefines … <child> <src>.gateValue` (`hR0`), `ChildBnd mref cref w`
(`hB`). No successful run is claimed unconditionally. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionSatTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
open Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
open Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest

set_option maxHeartbeats 4000000 in
/-- `hierGate` of `collMixSame`'s full-entry module, from the core run (`core_hierGateMT`). -/
theorem collMixSame_gate {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame
      (collMixSame.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Sparkle.IR.RefineCheck.hierGate b = true :=
  Tools.ShippingMemKid.core_hierGateMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    hB hcore hpost entry (collMixSame_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- No input of `collMixSame`'s full-entry module has an output's (sanitized) name (`TypedIn.oi`). -/
theorem collMixSame_oi {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame
      (collMixSame.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name :=
  (Tools.ShippingMemKid.core_closed_typedInMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixSame_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame_outChars o ho))
    (by first | decide | decide +kernel)).oi

set_option maxHeartbeats 4000000 in
/-- The inputs of `collMixSame`'s full-entry module (not `clk` / `rst`, positive width) are wires
(`inputWires_runMT`). -/
theorem collMixSame_inputWires {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``collMixSame [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``collMixSame
      (collMixSame.machineData).shape)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires :=
  Tools.ShippingInputWiresRun.inputWires_runMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixSame_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- `hierGate` of `collMixDiff`'s full-entry module, from the core run (`core_hierGateMT`). -/
theorem collMixDiff_gate {mctx : Lean.Meta.Context}
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
    Sparkle.IR.RefineCheck.hierGate b = true :=
  Tools.ShippingMemKid.core_hierGateMT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    hB hcore hpost entry (collMixDiff_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- No input of `collMixDiff`'s full-entry module has an output's (sanitized) name (`TypedIn.oi`). -/
theorem collMixDiff_oi {mctx : Lean.Meta.Context}
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
    ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name :=
  (Tools.ShippingMemKid.core_closed_typedInMT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixDiff_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixDiff_outChars o ho))
    (by first | decide | decide +kernel)).oi

set_option maxHeartbeats 4000000 in
/-- The inputs of `collMixDiff`'s full-entry module (not `clk` / `rst`, positive width) are wires
(`inputWires_runMT`). -/
theorem collMixDiff_inputWires {mctx : Lean.Meta.Context}
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
    ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires :=
  Tools.ShippingInputWiresRun.inputWires_runMT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixDiff_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- `hierGate` of `collMixArgs`'s full-entry module, from the core run (`core_hierGateMT`). -/
theorem collMixArgs_gate {mctx : Lean.Meta.Context}
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
    Sparkle.IR.RefineCheck.hierGate b = true :=
  Tools.ShippingMemKid.core_hierGateMT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    hB hcore hpost entry (collMixArgs_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- No input of `collMixArgs`'s full-entry module has an output's (sanitized) name (`TypedIn.oi`). -/
theorem collMixArgs_oi {mctx : Lean.Meta.Context}
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
    ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name :=
  (Tools.ShippingMemKid.core_closed_typedInMT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixArgs_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixArgs_outChars o ho))
    (by first | decide | decide +kernel)).oi

set_option maxHeartbeats 4000000 in
/-- The inputs of `collMixArgs`'s full-entry module (not `clk` / `rst`, positive width) are wires
(`inputWires_runMT`). -/
theorem collMixArgs_inputWires {mctx : Lean.Meta.Context}
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
    ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires :=
  Tools.ShippingInputWiresRun.inputWires_runMT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixArgs_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- `hierGate` of `collWidth`'s full-entry module, from the core run (`core_hierGateMT`). -/
theorem collWidth_gate {mctx : Lean.Meta.Context}
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
    Sparkle.IR.RefineCheck.hierGate b = true :=
  Tools.ShippingMemKid.core_hierGateMT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    hB hcore hpost entry (collWidth_closesR hR0)

set_option maxHeartbeats 4000000 in
/-- No input of `collWidth`'s full-entry module has an output's (sanitized) name (`TypedIn.oi`). -/
theorem collWidth_oi {mctx : Lean.Meta.Context}
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
    ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name :=
  (Tools.ShippingMemKid.core_closed_typedInMT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collWidth_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collWidth_outChars o ho))
    (by first | decide | decide +kernel)).oi

set_option maxHeartbeats 4000000 in
/-- The inputs of `collWidth`'s full-entry module (not `clk` / `rst`, positive width) are wires
(`inputWires_runMT`). -/
theorem collWidth_inputWires {mctx : Lean.Meta.Context}
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
    ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires :=
  Tools.ShippingInputWiresRun.inputWires_runMT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collWidth_closesR hR0)

end Sparkle.Tests.Compiler.MemNameCollisionSatTest

/-! ## The wiring-exporting endpoints, by the generator (the kernel checks the results) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  let sn := `Sparkle.Tests.Compiler.MemNameCollisionSatTest
  -- the same table as `MemNameCollisionGateBoundTest`
  for (p, cC, src, eqN, fN, tN, rN) in [(`collMixSame, `syncName, `fakeSrc, `syncGate_value, cn, yn, ns),
      (`collMixDiff, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collMixArgs, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collWidth, `comboName, `fakeN, `comboGate_value, an, an, an)] do
    let n ← Tools.ShippingGateTypedCommandW.generateTopW
      { parent := ns ++ p, name := sn ++ p.appendAfter "_designClosedBW",
        childConst := ns ++ cC, gateValue := ns ++ src ++ `gateValue,
        valueEq? := some (ns ++ eqN),
        runFacts := fN ++ p.appendAfter "_runFacts", outsG0 := fN ++ p.appendAfter "_outsG0",
        typedRun := tN ++ p.appendAfter "_typedRun", designP0 := fN ++ p.appendAfter "_designP0",
        closesR := rN ++ p.appendAfter "_closesR",
        head := ``Tools.ShippingNoPortsTyped.machine_design_noPortsTBW,
        names? := some (bn ++ p.appendAfter "_names") }
    Lean.logInfo m!"GATESAT [{n}]: head machine_design_noPortsTBW (composed from {p}.machine_composedTRGAW)"

/-! ## The satisfaction theorems (one elaborated term each; the statement is its type) -/

/-- Elaborate `stx`, require no metavariables, add it as theorem `name` (kernel-checked). -/
def addSat (name : Lean.Name) (stx : Lean.Term) : Lean.Elab.TermElabM Unit := do
  let e ← Lean.Elab.Term.elabTerm stx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  if e.hasMVar then throwError "{name}: the term has metavariables"
  let ty ← Lean.instantiateMVars (← Lean.Meta.inferType e)
  if ty.hasMVar then throwError "{name}: the statement has metavariables"
  Tools.ShippingMachineLinkedCommand.addTheorem name ty e

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (writing-time guess, accepted by build sa1/sa2: the implicit binders `fun {x : T} =>` elaborate as written, and the
  -- higher-order arguments `src`/`ext`/`extB` of `sat_of_designClosedBW` are found by unification
  -- with the generated `collMixSame_designClosedBW`)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_sat (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixSame.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssembly.sat_of_designClosedBW
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_designClosedBW hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixSame_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixSame_kidsSat hcore hpost entry hR0 hB)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (writing-time guess, accepted by build sa1/sa2: the implicit binders `fun {x : T} =>` elaborate as written, and the
  -- higher-order arguments `src`/`ext`/`extB` of `sat_of_designClosedBW` are found by unification
  -- with the generated `collMixDiff_designClosedBW`)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_sat (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixDiff.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssembly.sat_of_designClosedBW
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_designClosedBW hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixDiff_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixDiff_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixDiff_kidsSat hcore hpost entry hR0 hB)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (writing-time guess, accepted by build sa1/sa2: the implicit binders `fun {x : T} =>` elaborate as written, and the
  -- higher-order arguments `src`/`ext`/`extB` of `sat_of_designClosedBW` are found by unification
  -- with the generated `collMixArgs_designClosedBW`)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_sat (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collMixArgs.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.syncName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeSrc.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssembly.sat_of_designClosedBW
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_designClosedBW hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixArgs_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixArgs_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixArgs_kidsSat hcore hpost entry hR0 hB)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (writing-time guess, accepted by build sa1/sa2: the implicit binders `fun {x : T} =>` elaborate as written, and the
  -- higher-order arguments `src`/`ext`/`extB` of `sat_of_designClosedBW` are found by unification
  -- with the generated `collWidth_designClosedBW`)
  addSat `Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_sat (← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth
        (Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.collWidth.machineData).shape)
      (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.comboName
        Sparkle.Tests.Compiler.MemNameCollisionGateCertTest.fakeN.gateValue)
      (hB : Tools.ShippingChildInv.ChildBnd mref cref w) =>
    Tools.ShippingSatAssembly.sat_of_designClosedBW
      (Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_designClosedBW hr entry hR0) hB
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collWidth_names hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_gate hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_oi hcore hpost entry hR0 hB)
      (fun hcore hpost => Sparkle.Tests.Compiler.MemNameCollisionSatTest.collWidth_inputWires hcore hpost entry hR0 hB)
      (fun hcore hpost =>
        Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collWidth_kidsSat hcore hpost entry hR0 hB)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (by first | decide | decide +kernel)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by first | decide | decide +kernel)))

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let sn := `Sparkle.Tests.Compiler.MemNameCollisionSatTest
  for n in [``Tools.ShippingNoPortsTyped.machine_design_noPortsTBW,
      ``Tools.ShippingMachineCallsLinkedTG.machine_linkedT_callsRGW,
      ``Tools.ShippingComposedGW.composedGW_of_T, ``Tools.ShippingSatAssembly.sat_of_designClosedBW,
      ``Tools.ShippingSatInputs.sourceInputs_of_env, ``Tools.ShippingInputWiresRun.inputWires_runMT] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  for p in [`collMixSame, `collMixDiff, `collMixArgs, `collWidth] do
    for suf in ["_designClosedBW", "_gate", "_oi", "_inputWires", "_sat"] do
      Tests.Compiler.NoPortsTest.stdAxioms (sn ++ p.appendAfter suf)
    let t := (← Lean.getConstInfo (sn ++ p.appendAfter "_sat")).type
    -- the remaining premises: hr, entry, hR0, hB (and the implicit contexts) — nothing about
    -- the children, the start state or the input stream
    for k in [``Tools.ShippingDesignSVBounds.InvN, ``Tools.ShippingMachineShipsHier.Reset1,
        ``Tools.ShippingSeqOptSoundness.seedIn] do
      let prem ← Lean.Meta.forallTelescope t fun xs _ => do
        let mut found := false
        for x in xs do
          if ((← Lean.Meta.inferType x).find? (·.isConstOf k)).isSome then found := true
        pure found
      if prem then throwError "{p}_sat: a premise mentions {k}"
    Lean.logInfo m!"GATESAT {p}_sat: {t}"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionSatTest.collMixSame_sat
