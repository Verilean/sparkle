import Tests.Compiler.OneOutCallerTest
import Tools.ShippingGatePorts
import Tools.ShippingOneOutConns
import Tools.ShippingPortsMatchShipped
import Tools.ShippingHierGateAny

/-! # `caller` / `pick`: WRITTEN derivations of the two residual conditions (G1, round par/a-7)

`caller.machine_design_svH_free` (`Tests/Compiler/OneOutCallerTest.lean`)
keeps TWO INDEPENDENT check conditions as premises:

    (R1) hierTyped   (childMap D.modules) b                   = true
    (R2) portsMatchB (childMap D.modules) (checkedOptimize b) = true

This file instantiates the general theorems of this round at `caller`'s
data and at the gate child `pick`:

* `pick_ports`: `GateChildPorts ``pick pick.gateBinders pick.gateSort.width`
  of every real child of `pick` (`gate_real_ports`); `pick_width`: that
  width is `8`.
* `caller_portsRaw`: `portsMatchB (childMap D.modules) b` (`core_portsMatch_raw₁`).
* `caller_portsShipped`: (R2), by `portsMatchB_shipped` under the gate
  `core_hierGate_any`.
* `caller_hierTyped`: (R1) (`core_hierTyped₁`).
* `caller_designFull`: `designCheck (childMap D.modules) 0 (checkedOptimize b)`
  with no check premise (`core_designCheckH` fed with `caller_portsShipped`).

Each has the premises: the core run, the post-processing fact, `caller`'s
reflection and closing, `ChildBnd` of the start world, `pick`'s reflection
— the form the `typed` / `design` slots of `#machine_design_svH_free` take.

STATUS. Everything here is WRITTEN, not built. THE ENDPOINT IS NOT
REGENERATED in this file: `caller.machine_design_svH_free` still has the two
conditions as premises, and no premise counts as removed. Once the
integrator has built this file, the switch is: in `OneOutCallerTest`, give
the command the residual `(fun _ _ => True)` and the theorems
`[caller_factsH, caller_hierTyped, caller_designFull, caller_outsH]` (the
generator then REFUSES a re-run against the old statement, by its contract,
so the old command line is replaced, not kept beside it), then read the
complete premise list again.

DATA CONDITIONS decided per declaration here (kernel `decide` / `rfl`;
they are conditions on the reflected data of `caller` and `pick`, not
reductions): those of `OneOutCallerTest`; `callArgsOk caller.machineData 1
kidIns` with `kidIns` the widths of `pick`'s declared non-domain binders
(the widths of the types of `caller`'s `let` binders of the call's
arguments equal `pick`'s argument widths — nothing in the compiler compares
them); the width of the type of `caller`'s binder of the call's result is
`8`; `pick.gateSort.width = 8`.

SCOPE: `caller` only (a parent WITH a register; `core_portsMatch_raw₁` and
`core_hierTyped₁` themselves do not use `slots ≠ []`, the head does), child
`pick` (gate route). Slotless parents, machine-route children and "all
successful inputs" are not covered.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutCallerPortsTest
open Sparkle.Tests.Compiler.ShippingMachineInstTest
open Tests.Compiler.OneOutCallerTest

/-- The argument widths of `pick`: the widths of the types of its declared
non-domain binders, for every call entry of `caller`. -/
noncomputable def kidIns : Nat → List Nat := fun _ =>
  (pick.gateBinders.filter fun x => x.2 != .domain).map fun x =>
    (Tools.ShippingMachineEntry.kindTy x.2).bitWidth

/-- The common port facts of every real child of `pick`. -/
theorem pick_ports {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pick y) :
    Tools.ShippingGatePorts.GateChildPorts ``pick pick.gateBinders
      (Tools.ShippingUnifiedSource.SType.width pick.gateSort) y.1 :=
  Tools.ShippingGatePorts.gate_real_ports hR0 pick.gate_old pick.gate_peel pick.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy

/-- `pick`'s result is eight bits. -/
theorem pick_width : Tools.ShippingUnifiedSource.SType.width pick.gateSort = 8 := by
  first
    | rfl
    | decide

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `caller`'s full-entry module, from the run**
(`core_portsMatch_raw₁` at `caller`'s data, the child-side facts from
`pick_ports`). No check premise. -/
theorem caller_portsRaw {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_portsMatch_raw₁ (nDecl := 1) caller.machineData
    caller.machine_ok caller.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    rfl
    (by decide) (by decide)
    (by
      intro k hk y hy p hp
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        have hw := (pick_ports hR0 hy).outWidth p hp
        rw [hw.2, pick_width]
        first
          | decide
          | rfl
      | succ k => exact absurd hk' (by omega))
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact (pick_ports hR0 hy).portsIn
      | succ k => exact absurd hk' (by omega))
    (kidIns := kidIns) (by decide)
    (by
      intro k hk y hy j q hq
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        obtain ⟨wd, h1, h2, -⟩ := (pick_ports hR0 hy).inWidths hq
        exact ⟨wd, h1, h2⟩
      | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ caller.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho))
    (by decide)

set_option maxHeartbeats 0 in
/-- **(R2) `portsMatchB` of `caller`'s SHIPPED module, from the run.** -/
theorem caller_portsShipped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingPortsMatchShipped.portsMatchB_shipped
    (Tools.ShippingHierGateAny.core_hierGate_any (nDecl := 1) caller.machineData
      caller.machine_ok caller.machine_body (by decide) (by decide) (by decide)
      (fun h0 => absurd (congrArg List.length h0) (by decide))
      (by decide) (by decide)
      hB hcore hpost entry closes)
    (caller_portsRaw hcore hpost entry closes hB hR0)

set_option maxHeartbeats 0 in
/-- **(R1) `hierTyped` of `caller`'s full-entry module, from the run**
(`core_hierTyped₁` at `caller`'s data, the child-side facts from
`pick_ports`). No check premise. -/
theorem caller_hierTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue) :
    Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_hierTyped₁ (nDecl := 1) caller.machineData
    caller.machine_ok caller.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    rfl
    (by decide) (by decide)
    (by
      intro k hk y hy p hp
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        have hw := (pick_ports hR0 hy).outWidth p hp
        rw [hw.2, pick_width]
        first
          | decide
          | rfl
      | succ k => exact absurd hk' (by omega))
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact (pick_ports hR0 hy).childTyped_ok
      | succ k => exact absurd hk' (by omega))
    (kidIns := kidIns) (by decide)
    (by
      intro k hk y hy j q hq
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        obtain ⟨wd, h1, -, h3⟩ := (pick_ports hR0 hy).inWidths hq
        exact ⟨wd, h1, h3⟩
      | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ caller.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho))
    (by decide)

set_option maxHeartbeats 0 in
/-- **`designCheck` of `caller`'s shipped module at depth 0, from the run,
with no check premise** (`caller_designH` fed with `caller_portsShipped`). -/
theorem caller_designFull {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  caller_designH hcore hpost entry closes hB hR0
    (caller_portsShipped hcore hpost entry closes hB hR0)

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let std (n : Name) : MetaM Unit := do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  for n in [``Tools.ShippingTypedWidthOk.typed_widthOk,
      ``Tools.ShippingTypedWidthOk.assignTyped_of_typed,
      ``Tools.ShippingTypedWidthOk.connsTyped_call,
      ``Tools.ShippingGatePorts.gate_child_base, ``Tools.ShippingGatePorts.gate_real_ports,
      ``Tools.ShippingGatePorts.gate_real_outWidth,
      ``Tools.ShippingGatePorts.GateChildPorts.portsIn,
      ``Tools.ShippingGatePorts.GateChildPorts.inWidths,
      ``Tools.ShippingGatePorts.GateChildPorts.childTyped_ok,
      ``Tools.ShippingOneOutConns.core_callConns₁,
      ``Tools.ShippingOneOutConns.core_portsMatch_raw₁,
      ``Tools.ShippingOneOutConns.core_hierTyped₁,
      ``pick_ports, ``caller_portsRaw, ``caller_portsShipped, ``caller_hierTyped,
      ``caller_designFull] do
    std n
  -- the derived statements mention no checker constant in a PREMISE: each
  -- theorem's binder types are scanned for the eight checker constants
  let checkers := Tools.ShippingOneOutCommand.forbidden ++ Tools.ShippingOneOutCommand.residualOnly
  for n in [``caller_hierTyped, ``caller_portsShipped, ``caller_designFull] do
    let t := (← getConstInfo n).type
    let hits ← forallTelescope t fun xs _ => do
      let mut acc : List Name := []
      for x in xs do
        let tx ← instantiateMVars (← inferType x)
        acc := acc ++ Tools.ShippingOneOutCommand.mentioned checkers tx
      return acc
    unless hits.isEmpty do
      throwError "{n}: a premise mentions {hits}"
    let hid ← Tools.ShippingOneOutCommand.hidden checkers Tools.ShippingOneOutCommand.hiddenFuel
      false false t
    unless hid.isEmpty do
      throwError "{n}: a premise hides {hid} inside a definition"
  logInfo m!"ONEOUT WRITTEN caller: hierTyped (caller_hierTyped) and portsMatchB of the shipped module (caller_portsShipped) stated with premises the core run, the post-processing fact, caller's reflection and closing, ChildBnd, pick's reflection; data conditions decided here: callArgsOk caller.machineData 1 kidIns (kidIns: the widths of the declared non-domain binders of pick), the result binder's width, pick.gateSort.width = 8. The endpoint caller.machine_design_svH_free is NOT regenerated: its two residual conditions are still premises. Standard axioms."

end Tests.Compiler.OneOutCallerPortsTest
