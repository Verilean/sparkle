import Tests.Compiler.OneOutCallerFullTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tools.ShippingLeafOneOut
import Tools.ShippingOneOutConns
import Tools.ShippingOneOutFullCommand
import Tools.ShippingPortsMatchShipped
import Tools.ShippingHierGateAny
import Tools.ShippingChecksCoreGate
import Tools.ShippingCallWidthsStrict
import Tools.ShippingFinalGoalCommand
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # ONE endpoint, `callerL` (child `pickByteH`, a SLOTLESS MACHINE-route leaf): the one-output head by hand (G1, round par/a-10)

`Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL`: a `circuit do`
WITH a register (`sel : BitVec 2`), ONE call entry `pickByteH w selS`,
returning the call's result (`BitVec 8`); `instFields = []` (the one-output
closing `closeInsts`). The child `pickByteH` is compiled by the MACHINE
route: three hardware `let`s, no register, no call, the one output `out`.
(Read off the source; every such fact used below is a kernel `decide` /
`rfl` on the reflected data — a wrong reading makes a theorem fail, it
proves nothing false.)

Starting endpoint: `callerL.machine_design_svHR` (BUILT earlier), whose four
check premises under `∃ raw D` are `shipsHierHCheck D.modules b`,
`kidsComb D.modules (checkedOptimize b).body`,
`designCheck (childMap D.modules) 0 (checkedOptimize b)`,
`outsCheck (childMap D.modules) 0 (checkedOptimize b)`.

## What is here

The child-side hypotheses of the general theorems, each as its own named
theorem about every real child of `pickByteH`, all read off ONE bundle
`pickByteH_leaf : SlotlessLeaf … pickByteH pickByteH.machineData`
(`Tools/ShippingLeafOneOut.lean`):

    pickByteH_outTys      the output ports are the layout's          (for hkidW)
    pickByteH_portsIn     PortsIn y.1                                (hkidT)
    pickByteH_inWidths    the j-th input port's width, BOTH tables   (hkidIn, hkidInD)
    pickByteH_childTyped  childTyped (declWidth y.1) y.1             (hkidTy)
    pickByteH_kidK        the children's text check                  (hkidK)
    pickByteH_kidA / _kidR  outputs assigned / no instance statement (hkidA, hkidR)

then the four theorems of the head at `callerL`'s data (`callerL_factsH`,
`callerL_hierTyped`, `callerL_designFull`, `callerL_outsH`; with
`callerL_portsRaw`, `callerL_portsShipped` between), and the endpoint by the
EXISTING command `#machine_design_svH_full callerL [...]`.

## EXPECTED (stated before the build)

`SVHFULL GENERATED [callerL.machine_design_svH_full,
callerL.machine_design_svH_full_closed]`; the closed form's premises: the
run `RunsTo (synthesizeCombinational callerL) …`, `MachineDefines` of
`callerL`, `MachineDefines` of `pickByteH` (the one premise of
`callerL.machine_closes_at` — where a gate child has `EntryDefines`), and
under `∃ raw D`: `ChildBnd mref cref w`, `MachineDefines` of `pickByteH`.
Class `other`: NONE on the closed form, the closing premise only on the open
form. The test throws otherwise.

## DATA CONDITIONS decided per declaration (kernel `decide` / `rfl`; conditions, not reductions)

For `callerL` (`callerL.machineData`, `nDecl = 1`): `callsOk 1`
(`callerL_callsOk`); `ss.length = shape.layout.slots.length`
(`callerL_slotLen`); no domain binder after the first (`callerL_domB`);
`shape.insts ≠ []` (`callerL_insts`); `shape.instFields = []`
(`callerL_instFields`); every output's `ty.bitWidth = width`
(`callerL_outTy`); no memory callee (`callerL_nomem`);
`shape.layout.slots ≠ []` — the PARENT has a register (`callerL_slots`); the
output names character-wise `charOk` (`callerL_outChars`); the output types
`scalarTy` (`callerL_outScalar`); `callWidthsStrict callerL.machineData 1
(fun _ => pickByteH.machineData.shape.layout.outs)` — the width of the type
of the binder of the call's result is the width of `pickByteH`'s output
field (`callerL_strict`); `callArgsOk callerL.machineData 1 kidIns` with
`kidIns` the declared widths of `pickByteH` (`callerL_callArgs`: the widths
of the types of `callerL`'s `let` binders of the call's arguments are
`pickByteH`'s argument widths — nothing in the compiler compares them); the
one entry's callee is `pickByteH` (by reduction, where `hy` is used).

For `pickByteH` (`pickByteH.machineData`, at `nIn`): the fields of
`pickByteH_leaf` other than its reflection and closing — `ok`
(`pickByteH.machine_ok`), the body equation, `callsOk nIn`, no domain binder
after `nIn`, `insts = []` (a LEAF), the slot count, every output's
`ty.bitWidth = width`, the output names `charOk`, the output types
`scalarTy`, `gateCallsOk nIn`, `layout.lets ≠ 0`, `layout.slots = []`
(SLOTLESS), the one output `out`. Its own closing is the generated
`pickByteH.machine_closes` (with its own decided conditions).

Plus those of the generators run before (`callerL.machine_ships_hierHR`,
`callerL.machine_closes_at`).

## SCOPE (binding for any report)

ONE declaration, `callerL`: a parent WITH a register (the head needs
`slots ≠ []`), one call entry, a child that is a SLOTLESS LEAF MACHINE with
the one output `out`, the one-output closing. The runtime boundary stays
premises (the run, `MachineDefines callerL`, `MachineDefines pickByteH`,
`ChildBnd`; no runtime model). The result depends on the compiler's guards
(`checkedOptimize`'s fallback, `deinline`'s guards, `closeInsts`' checks,
`mergeChecked`'s validation). The conclusion is about
`DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module list, not
the SV string, not `#sim`. NOT covered: slotless PARENTS, machine children
with registers or with calls, several outputs, any other declaration
(`callerLN`, `hftByte` were not instantiated), "all successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutCallerLTest
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest

/-! ## The child `pickByteH` -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The bundle of `pickByteH`'s per-declaration conditions**, given its
reflection in the run's contexts. Every field but `entry` is decided here or
is a generated theorem of `pickByteH`. -/
theorem pickByteH_leaf {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingLeafOneOut.SlotlessLeaf mctx mref cctx cref ``pickByteH pickByteH.machineData :=
  { any :=
      { ok := pickByteH.machine_ok
        body := pickByteH.machine_body
        calls := by decide
        dom := by decide
        leaf := by first | rfl | decide
        ss := by decide
        outTy := by decide
        outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          ((show ∀ o ∈ pickByteH.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
              Sparkle.IR.NameHints.charOk c = true from by
            first | decide | decide +kernel) o ho)
        outScalar := by decide
        entry := hR0
        closes := fun mc cc => pickByteH.machine_closes mc _ cc _ }
    gate := by decide
    lets := by decide
    slots := by first | rfl | decide
    one := ⟨_, rfl, rfl⟩ }

/-- The output ports of a real child of `pickByteH` are its layout's. -/
theorem pickByteH_outTys {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y) :
    Tools.ShippingChildIfaceTy.ChildOutTys pickByteH.machineData.shape.layout.outs y.1 :=
  (pickByteH_leaf hR0).outTys hy

/-- (`hkidT`) The emitter's width map resolves `pickByteH`'s output port. -/
theorem pickByteH_portsIn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y) :
    Tools.ShippingLeafTyped.PortsIn y.1 :=
  (pickByteH_leaf hR0).portsIn hy

/-- (`hkidIn`, `hkidInD`) The `j`-th input port of a real child of
`pickByteH` has the `j`-th declared width in the emitter's table AND in the
IR's. -/
theorem pickByteH_inWidths {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y)
    {j : Nat} {q : Sparkle.IR.AST.Port} (hq : y.1.inputs[j]? = some q) :
    ∃ wd, (Tools.ShippingPortWidthsPure.declWidths pickByteH.machineData)[j]? = some wd ∧
      Tools.ShippingDesignSV.weS y.1 q.name = wd ∧
      Sparkle.IR.RegDedup.declWidth y.1 q.name = wd :=
  (pickByteH_leaf hR0).inWidths hy hq

/-- (`hkidTy`) A real child of `pickByteH` is a width-typed child in its own
declared widths. -/
theorem pickByteH_childTyped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y) :
    Tools.ShippingHierTyped.childTyped (Sparkle.IR.RegDedup.declWidth y.1) y.1 = true :=
  (pickByteH_leaf hR0).childTyped hy

/-- (`hkidK`) The children's text check of a real child of `pickByteH`. -/
theorem pickByteH_kidK {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true :=
  (pickByteH_leaf hR0).kidK hy

/-- (`hkidA`) A real child of `pickByteH` assigns its output; its design is
empty. -/
theorem pickByteH_kidA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true :=
  (pickByteH_leaf hR0).kidA hy

/-- (`hkidR`) A real child of `pickByteH` has no instance statement. -/
theorem pickByteH_kidR {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pickByteH y) :
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn :=
  (pickByteH_leaf hR0).kidR hy

/-! ## The parent `callerL`: the data conditions, each named -/

set_option maxRecDepth 100000 in
theorem callerL_callsOk :
    Tools.ShippingMachineAuto.MachineData.callsOk callerL.machineData 1 = true := by decide

set_option maxRecDepth 100000 in
theorem callerL_slotLen :
    callerL.machineData.ss.length = callerL.machineData.shape.layout.slots.length := by decide

set_option maxRecDepth 100000 in
theorem callerL_domB : ∀ b ∈ callerL.machineData.shape.binders.drop 1,
    b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain := by decide

theorem callerL_insts : callerL.machineData.shape.insts ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

theorem callerL_instFields : callerL.machineData.shape.instFields = [] := by
  first | rfl | decide

set_option maxRecDepth 100000 in
theorem callerL_outTy : ∀ o ∈ callerL.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  decide

set_option maxRecDepth 100000 in
theorem callerL_nomem : ∀ x ∈ callerL.machineData.shape.instTagged, x.2.child?.isNone = true ∧
    (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true := by decide

/-- The PARENT has a register. -/
theorem callerL_slots : callerL.machineData.shape.layout.slots ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

set_option maxRecDepth 100000 in
theorem callerL_outChars : ∀ o ∈ callerL.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem callerL_outClean : ∀ o ∈ callerL.machineData.shape.layout.outs,
    Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
  fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (callerL_outChars o ho)

set_option maxRecDepth 100000 in
theorem callerL_outScalar : ∀ o ∈ callerL.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by decide

set_option maxRecDepth 100000 in
/-- The width of the type of the binder of the call's result is the width
of `pickByteH`'s output field (the strict condition: with no field list,
every output of the child is compared). -/
theorem callerL_strict :
    Tools.ShippingCallWidthsStrict.callWidthsStrict callerL.machineData 1
      (fun _ => pickByteH.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

/-- The argument widths of `pickByteH`: its declared widths, for every call
entry of `callerL`. -/
noncomputable def kidIns : Nat → List Nat := fun _ =>
  Tools.ShippingPortWidthsPure.declWidths pickByteH.machineData

set_option maxRecDepth 100000 in
/-- The widths of the types of `callerL`'s `let` binders of the call's
arguments are `pickByteH`'s declared widths. -/
theorem callerL_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk callerL.machineData 1 kidIns = true := by
  first | decide | decide +kernel

/-- (`hkidW`) Every output port of a real child of the call has the width of
the type of the call's binder. -/
theorem callerL_kidW {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    ∀ (k : Nat) (hk : k < callerL.machineData.shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildInv.RealChild mref cref (callerL.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs,
        (callerL.machineData.shape.binders[1 + k]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some p.ty.bitWidth :=
  Tools.ShippingPortsMatchRawLeafAny.hkidW_one
    (kidOuts := fun _ => pickByteH.machineData.shape.layout.outs) callerL_instFields
    callerL_strict
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact pickByteH_outTys hR0 hy
      | succ k => exact absurd hk' (by omega))

/-! ## The four theorems of the head -/

set_option maxHeartbeats 0 in
/-- **The run's facts of `callerL`'s full-entry module** (`core_runFactsH`). -/
theorem callerL_factsH {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerL [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingOneOutFacts.RunFactsH D.modules b :=
  Tools.ShippingOneOutFacts.core_runFactsH (nDecl := 1) callerL.machineData
    callerL.machine_ok callerL.machine_body callerL_callsOk callerL_slotLen callerL_domB
    callerL_insts callerL_instFields callerL_outTy callerL_nomem
    hB hcore hpost entry closes callerL_slots

set_option maxHeartbeats 0 in
/-- **`outsCheck` of `callerL`'s shipped module at depth 0, from the run**
(`core_outsCheck_all_gate`; the child's facts from `pickByteH_kidA` /
`pickByteH_kidR`), under the statement-kind gate. No check premise. -/
theorem callerL_outsH {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerL [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := 1) callerL.machineData
    callerL.machine_ok callerL.machine_body callerL_callsOk callerL_slotLen callerL_domB
    callerL_insts callerL_outTy callerL_nomem
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact pickByteH_kidA hR0 hy
      | succ k => exact absurd hk' (by omega))
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact pickByteH_kidR hR0 hy
      | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes hg 0

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `callerL`'s full-entry module, from the run**
(`core_portsMatch_raw₁`; the child-side facts from `pickByteH_*`). -/
theorem callerL_portsRaw {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerL [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_portsMatch_raw₁ (nDecl := 1) callerL.machineData
    callerL.machine_ok callerL.machine_body callerL_callsOk callerL_slotLen callerL_domB
    callerL_insts callerL_instFields callerL_outTy callerL_nomem
    (callerL_kidW hR0)
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact pickByteH_portsIn hR0 hy
      | succ k => exact absurd hk' (by omega))
    (kidIns := kidIns) callerL_callArgs
    (by
      intro k hk y hy j q hq
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        obtain ⟨wd, h1, h2, -⟩ := pickByteH_inWidths hR0 hy hq
        exact ⟨wd, h1, h2⟩
      | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes callerL_outClean callerL_outScalar

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `callerL`'s SHIPPED module, from the run.** -/
theorem callerL_portsShipped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerL [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingPortsMatchShipped.portsMatchB_shipped
    (Tools.ShippingHierGateAny.core_hierGate_any (nDecl := 1) callerL.machineData
      callerL.machine_ok callerL.machine_body callerL_callsOk callerL_slotLen callerL_domB
      callerL_insts callerL_outTy callerL_nomem
      hB hcore hpost entry closes)
    (callerL_portsRaw hcore hpost entry closes hB hR0)

set_option maxHeartbeats 0 in
/-- **`hierTyped` of `callerL`'s full-entry module, from the run**
(`core_hierTyped₁`; the child-side facts from `pickByteH_*`). No check
premise. -/
theorem callerL_hierTyped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerL [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_hierTyped₁ (nDecl := 1) callerL.machineData
    callerL.machine_ok callerL.machine_body callerL_callsOk callerL_slotLen callerL_domB
    callerL_insts callerL_instFields callerL_outTy callerL_nomem
    (callerL_kidW hR0)
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact pickByteH_childTyped hR0 hy
      | succ k => exact absurd hk' (by omega))
    (kidIns := kidIns) callerL_callArgs
    (by
      intro k hk y hy j q hq
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        obtain ⟨wd, h1, -, h3⟩ := pickByteH_inWidths hR0 hy hq
        exact ⟨wd, h1, h3⟩
      | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes callerL_outClean callerL_outScalar

set_option maxHeartbeats 0 in
/-- **`designCheck` of `callerL`'s shipped module at depth 0, from the run,
with no check premise** (`core_designCheckH` fed with `callerL_portsShipped`;
the children's check by `pickByteH_kidK`). -/
theorem callerL_designFull {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerL [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerL
      callerL.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingOneOutFacts.core_designCheckH (nDecl := 1) callerL.machineData
    callerL.machine_ok callerL.machine_body callerL_callsOk callerL_slotLen callerL_domB
    callerL_insts callerL_instFields callerL_outTy callerL_nomem
    hB hcore hpost entry closes callerL_slots callerL_outClean callerL_outScalar
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact pickByteH_kidK hR0 hy
      | succ k => exact absurd hk' (by omega))
    0 (callerL_portsShipped hcore hpost entry closes hB hR0)

end Tests.Compiler.OneOutCallerLTest

/-! ## The endpoint, by the existing command -/

set_option maxHeartbeats 0 in
#machine_design_svH_full Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL
  [Tests.Compiler.OneOutCallerLTest.callerL_factsH,
   Tests.Compiler.OneOutCallerLTest.callerL_hierTyped,
   Tests.Compiler.OneOutCallerLTest.callerL_designFull,
   Tests.Compiler.OneOutCallerLTest.callerL_outsH]

#check @Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full
#check @Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL.machine_design_svH_full_closed

namespace Tests.Compiler.OneOutCallerLTest
open Lean Meta Elab Command

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL
  let kid := ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH
  let full := f ++ `machine_design_svH_full
  let closed := Tools.ShippingMachineClosesGen.closedName full
  let cl := f ++ `machine_closes_at
  let old := f ++ `machine_design_svHR
  let std (n : Name) : MetaM Unit := do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  unless (← getEnv).contains full do throwError "{full} was not generated"
  unless (← getEnv).contains closed do throwError "{closed} was not generated"
  -- (a) standard axioms: the endpoints, the hand theorems, the new general theorems
  for n in [full, closed, cl,
      ``pickByteH_leaf, ``pickByteH_outTys, ``pickByteH_portsIn, ``pickByteH_inWidths,
      ``pickByteH_childTyped, ``pickByteH_kidK, ``pickByteH_kidA, ``pickByteH_kidR,
      ``callerL_kidW, ``callerL_factsH, ``callerL_outsH, ``callerL_portsRaw,
      ``callerL_portsShipped, ``callerL_hierTyped, ``callerL_designFull,
      ``Tools.ShippingLeafOneOut.closeMachine_slotless_body,
      ``Tools.ShippingLeafOneOut.count_out_slotless,
      ``Tools.ShippingLeafOneOut.readsClosedB_of_all,
      ``Tools.ShippingLeafOneOut.typedIn_childTyped_out,
      ``Tools.ShippingLeafOneOut.childTyped_post_out,
      ``Tools.ShippingLeafOneOut.inPort_both,
      ``Tools.ShippingLeafOneOut.leafPorts_inWidths2,
      ``Tools.ShippingLeafOneOut.leafPorts_inPortsOf_eq,
      ``Tools.ShippingLeafTyped.leaf_run_typedIn_out,
      ``Tools.ShippingLeafTyped.leaf_real_typedIn_out,
      ``Tools.ShippingLeafOneOut.SlotlessLeaf.childTyped,
      ``Tools.ShippingLeafOneOut.SlotlessLeaf.inWidths,
      ``Tools.ShippingLeafOneOut.SlotlessLeaf.kidA,
      ``Tools.ShippingLeafOneOut.SlotlessLeaf.kidR] do
    std n
  -- (b) the eight checker constants: written, or hidden in a premise's definition
  let checkers := Tools.ShippingOneOutCommand.forbidden ++ Tools.ShippingOneOutCommand.residualOnly
  for n in [full, closed] do
    let t := (← getConstInfo n).type
    Tools.ShippingOneOutCommand.refuse n t (mkConst ``True)
    let hits := Tools.ShippingOneOutCommand.mentioned checkers t
    unless hits.isEmpty do
      throwError "{n}: the statement mentions {hits}"
    if Tools.ShippingOneOutFullCommand.trueAntecedent t then
      throwError "{n}: the trivially true residual is an antecedent"
  -- no premise of a hand theorem mentions or hides a checker
  for n in [``callerL_factsH, ``callerL_outsH, ``callerL_portsRaw, ``callerL_portsShipped,
      ``callerL_hierTyped, ``callerL_designFull] do
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
  -- (c) the inventory: the old endpoint asks the four check premises
  let oldT := (← getConstInfo old).type
  for c in [``Tools.ShippingHierPremises.shipsHierHCheck,
      ``Tools.ShippingMachineDepthH.kidsComb, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf c)).isSome do
      throwError "{old}: does not mention {c} (the inventory is wrong)"
  -- (d) the complete premise lists
  let (clLines, clOthers) ← Tests.Compiler.OneOutCallerFullTest.premiseList cl (inner := false)
  logInfo m!"{String.intercalate "\n" clLines.toList}"
  unless clOthers.isEmpty do
    throwError "{cl}: contributes premises that are not a run / a reflection / ChildBnd (NOT allowed):\n{String.intercalate "\n" (clOthers.toList.map (·.1))}"
  let (openLines, openOthers) ← Tests.Compiler.OneOutCallerFullTest.premiseList full
  logInfo m!"{String.intercalate "\n" openLines.toList}"
  unless openOthers.size == 1 && openOthers.all (·.2) do
    throwError "{full}: the premises of class other must be exactly the closing premise MachineClosesAt, found {openOthers.size}:\n{String.intercalate "\n" (openOthers.toList.map (·.1))}"
  let (closedLines, closedOthers) ← Tests.Compiler.OneOutCallerFullTest.premiseList closed
  logInfo m!"{String.intercalate "\n" closedLines.toList}"
  unless closedOthers.isEmpty do
    throwError "{closed}: premises of class other (must be none):\n{String.intercalate "\n" (closedOthers.toList.map (·.1))}"
  -- (e) the child's reflection is its MACHINE reflection, a binder of the closed form
  let closedT := (← getConstInfo closed).type
  let kidRefl ← forallTelescope closedT fun xs _ => do
    let mut found := false
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines &&
          (t.find? (·.isConstOf (kid ++ `machineData))).isSome then
        found := true
    return found
  unless kidRefl do
    throwError "{closed}: no MachineDefines binder of the child {kid}"
  if (closedT.find? (·.isConstOf ``Tools.ShippingInlineSoundness.EntryDefines)).isSome then
    throwError "{closed}: an EntryDefines premise appears — the child is not read as a machine-route child"
  -- (f) the goal gap of the closed form
  let gapName := match closed with
    | .str p s => Name.str p (s ++ "_gap")
    | n => n ++ `gap
  let report ← Tools.ShippingFinalGoalCommand.gapOf closed gapName
  logInfo m!"GOALGAP {gapName} from {closed}\n{String.intercalate "\n" report.toList}"
  let bad := report.filter fun l => (l.splitOn "NOT ALLOWED").length > 1
  unless bad.isEmpty do
    throwError "{closed}: the goal-gap reporter lists premises NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  std gapName
  logInfo m!"ONEOUT MACHINE-LEAF callerL: {full} ({openLines.size} lines; other: the closing premise only) and {closed} ({closedLines.size} lines; other: NONE) — none of the four check premises of {old} (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap {gapName}: {report.size} lines, none NOT ALLOWED. The child's premise is its MACHINE reflection (MachineDefines of pickByteH), not EntryDefines. SCOPE of this statement: (1) data conditions decided per declaration by the kernel — for callerL: callsOk 1, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [] (the parent has a register), output width / name / scalar conditions, no memory callee, callWidthsStrict against pickByteH's layout outputs (the result binder's width), callArgsOk against pickByteH's declared widths; for pickByteH (the fields of pickByteH_leaf): ok, the body equation, callsOk and no late domain binder at nIn, insts = [] (a leaf), the slot count, output width / name / scalar conditions, gateCallsOk at nIn, lets ≠ 0, slots = [] (slotless), the one output out, and its generated closing pickByteH.machine_closes — conditions, not reductions; (2) runtime boundary premises that remain: the run of the entry, MachineDefines of callerL, MachineDefines of pickByteH, ChildBnd (open form: also MachineClosesAt); (3) the result depends on the compiler's guards (checkedOptimize's fallback, deinline's guards, closeInsts' checks, mergeChecked's validation of the child's merge); (4) the conclusion is about DesignSV (childMap D.modules) 0 (checkedOptimize b) — the module list, not the SV string, not #sim; (5) ONE declaration: a parent with a register, one call of a slotless leaf machine child with the one output out, the one-output closing — not slotless parents, not machine children with registers or calls, not several outputs, not callerLN, not hftByte, not all successful inputs. Standard axioms."

end Tests.Compiler.OneOutCallerLTest
