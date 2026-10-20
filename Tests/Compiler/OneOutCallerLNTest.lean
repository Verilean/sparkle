import Tests.Compiler.OneOutCallerLTest
import Tests.Compiler.OneOutLeafAudit
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # ONE endpoint, `callerLN` (child `pickByteH`, a slotless machine-route leaf): the one-output head by hand (G1, round par/a-11)

`Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN`:

    circuit do
      let s := counterB en          -- a sub-machine (one register), flattened
      let acc ← Signal.reg 0#16
      let accS := (acc : Signal defaultDomain (BitVec 16))
      acc <~ accS ^^^ w
      return pickByteH accS s

READ off the source (every such fact used below is a kernel `decide` /
`rfl` on the reflected data — a wrong reading makes a NAMED theorem fail, it
proves nothing false): two declaration binders `w`, `en` (`nDecl = 2`); the
parent HAS registers (`acc`, and the flattened `counterB`'s `c`); one call
entry, `pickByteH accS s`, which is the returned value; `instFields = []`
(the one-output closing `closeInsts`); the one output `out : BitVec 8`.

The child is `callerL`'s: `pickByteH`, with its bundle `pickByteH_leaf` and
the seven `pickByteH_*` theorems of `Tests/Compiler/OneOutCallerLTest.lean`
(BUILT), reused unchanged. So this file has NO new fact about the child and
no new general theorem; what is new is the parent's data conditions at
`nDecl = 2`, each a named theorem:

    callerLN_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem,
    _slots (the PARENT has a register), _outChars, _outScalar,
    _entries  (every entry's callee is pickByteH — decided over all
               k < insts.length, no entry count written),
    _strict   (callWidthsStrict … 2 (fun _ => pickByteH's layout outputs):
               the result binder's width is the child's output width),
    _callArgs (callArgsOk … 2 kidIns, kidIns = declWidths pickByteH.machineData:
               the first argument is the register `acc` (16), the second the
               sub-machine's result `s` (2); by A-oneout §11.2 both are `let`s
               of the callee's kinds — a reading of the reader, the `decide`
               is what the theorem rests on).

Difference from the hand instance of `callerL`: the per-entry facts are NOT
proved by `cases k` against a literal count; `callerLN_entries` is decided
over every `k < insts.length` and rewritten with (the generator's pattern).

Starting endpoint: `callerLN.machine_design_svHR` (BUILT,
`Tests/Compiler/ShippingChildBoundaryTest.lean`), whose four check premises
under `∃ raw D` are `shipsHierHCheck D.modules b`,
`kidsComb D.modules (checkedOptimize b).body`,
`designCheck (childMap D.modules) 0 (checkedOptimize b)`,
`outsCheck (childMap D.modules) 0 (checkedOptimize b)`.

## EXPECTED (stated before the build)

`SVHFULL GENERATED [callerLN.machine_design_svH_full,
callerLN.machine_design_svH_full_closed]`; the closed form's premises: the
run, `MachineDefines` of `callerLN`, `MachineDefines` of `pickByteH`, and
under `∃ raw D`: `ChildBnd mref cref w`, `MachineDefines` of `pickByteH`.
Class `other`: NONE on the closed form, the closing premise only on the open
form. The test throws otherwise.

## SCOPE (binding for any report)

ONE declaration, `callerLN`: a parent WITH a register, one call entry, a
child that is a SLOTLESS LEAF MACHINE with the one output `out`, the
one-output closing. The data conditions above and `pickByteH_leaf`'s fields
are decided per declaration: conditions, not reductions. The runtime
boundary stays premises (the run, `MachineDefines callerLN`,
`MachineDefines pickByteH`, `ChildBnd`). The result depends on the
compiler's guards. The conclusion is about
`DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module list, not
the SV string, not `#sim`. NOT covered: slotless PARENTS, machine children
with registers or with calls, several outputs, "all successful inputs".

NAME CLASH, on purpose not hidden: `#machine_oneout_any callerLN`
(`Tests/Compiler/OneOutAnyFamilyTest.lean`) generates the SAME endpoint
name. The two files must not both be imported by one module unless the
family test imports this one (then it reports PRESENT, not GENERATED).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutCallerLNTest
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest

/-! ## The parent `callerLN`: the data conditions, each named -/

set_option maxRecDepth 100000 in
theorem callerLN_callsOk :
    Tools.ShippingMachineAuto.MachineData.callsOk callerLN.machineData 2 = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem callerLN_slotLen :
    callerLN.machineData.ss.length = callerLN.machineData.shape.layout.slots.length := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem callerLN_domB : ∀ b ∈ callerLN.machineData.shape.binders.drop 2,
    b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain := by
  first | decide | decide +kernel

theorem callerLN_insts : callerLN.machineData.shape.insts ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

theorem callerLN_instFields : callerLN.machineData.shape.instFields = [] := by
  first | rfl | decide

set_option maxRecDepth 100000 in
theorem callerLN_outTy : ∀ o ∈ callerLN.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem callerLN_nomem : ∀ x ∈ callerLN.machineData.shape.instTagged, x.2.child?.isNone = true ∧
    (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true := by
  first | decide | decide +kernel

/-- The PARENT has a register. -/
theorem callerLN_slots : callerLN.machineData.shape.layout.slots ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

set_option maxRecDepth 100000 in
theorem callerLN_outChars : ∀ o ∈ callerLN.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem callerLN_outClean : ∀ o ∈ callerLN.machineData.shape.layout.outs,
    Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
  fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (callerLN_outChars o ho)

set_option maxRecDepth 100000 in
theorem callerLN_outScalar : ∀ o ∈ callerLN.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- Every call entry's callee is `pickByteH` (decided over all
`k < insts.length`; no entry count is written). -/
theorem callerLN_entries : ∀ (k : Nat) (hk : k < callerLN.machineData.shape.insts.length),
    (callerLN.machineData.shape.insts[k]).1 = ``pickByteH := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The width of the type of the binder of every call's result is the width
of `pickByteH`'s output field (the strict condition: with no field list, every
output of the child is compared). -/
theorem callerLN_strict :
    Tools.ShippingCallWidthsStrict.callWidthsStrict callerLN.machineData 2
      (fun _ => pickByteH.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The widths of the types of `callerLN`'s `let` binders of every call's
arguments are `pickByteH`'s declared widths. -/
theorem callerLN_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk callerLN.machineData 2 Tests.Compiler.OneOutCallerLTest.kidIns = true := by
  first | decide | decide +kernel


/-- (`hkidW`) Every output port of a real child of a call has the width of
the type of the call's binder. -/
theorem callerLN_kidW {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    ∀ (k : Nat) (hk : k < callerLN.machineData.shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildInv.RealChild mref cref (callerLN.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs,
        (callerLN.machineData.shape.binders[2 + k]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some p.ty.bitWidth :=
  Tools.ShippingPortsMatchRawLeafAny.hkidW_one
    (kidOuts := fun _ => pickByteH.machineData.shape.layout.outs) callerLN_instFields
    callerLN_strict
    (by
      intro k hk y hy
      rw [callerLN_entries k hk] at hy
      exact Tests.Compiler.OneOutCallerLTest.pickByteH_outTys hR0 hy)

/-! ## The four theorems of the head -/

set_option maxHeartbeats 0 in
/-- **The run's facts of `callerLN`'s full-entry module** (`core_runFactsH`). -/
theorem callerLN_factsH {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerLN [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingOneOutFacts.RunFactsH D.modules b :=
  Tools.ShippingOneOutFacts.core_runFactsH (nDecl := 2) callerLN.machineData
    callerLN.machine_ok callerLN.machine_body callerLN_callsOk callerLN_slotLen callerLN_domB
    callerLN_insts callerLN_instFields callerLN_outTy callerLN_nomem
    hB hcore hpost entry closes callerLN_slots

set_option maxHeartbeats 0 in
/-- **`outsCheck` of `callerLN`'s shipped module at depth 0, from the run**
(`core_outsCheck_all_gate`), under the statement-kind gate. No check
premise. -/
theorem callerLN_outsH {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerLN [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := 2) callerLN.machineData
    callerLN.machine_ok callerLN.machine_body callerLN_callsOk callerLN_slotLen callerLN_domB
    callerLN_insts callerLN_outTy callerLN_nomem
    (by
      intro k hk y hy
      rw [callerLN_entries k hk] at hy
      exact Tests.Compiler.OneOutCallerLTest.pickByteH_kidA hR0 hy)
    (by
      intro k hk y hy
      rw [callerLN_entries k hk] at hy
      exact Tests.Compiler.OneOutCallerLTest.pickByteH_kidR hR0 hy)
    hB hcore hpost entry closes hg 0

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `callerLN`'s full-entry module, from the run**
(`core_portsMatch_raw₁`). -/
theorem callerLN_portsRaw {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerLN [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_portsMatch_raw₁ (nDecl := 2) callerLN.machineData
    callerLN.machine_ok callerLN.machine_body callerLN_callsOk callerLN_slotLen callerLN_domB
    callerLN_insts callerLN_instFields callerLN_outTy callerLN_nomem
    (callerLN_kidW hR0)
    (by
      intro k hk y hy
      rw [callerLN_entries k hk] at hy
      exact Tests.Compiler.OneOutCallerLTest.pickByteH_portsIn hR0 hy)
    (kidIns := Tests.Compiler.OneOutCallerLTest.kidIns) callerLN_callArgs
    (by
      intro k hk y hy j q hq
      rw [callerLN_entries k hk] at hy
      obtain ⟨wd, h1, h2, -⟩ := Tests.Compiler.OneOutCallerLTest.pickByteH_inWidths hR0 hy hq
      exact ⟨wd, h1, h2⟩)
    hB hcore hpost entry closes callerLN_outClean callerLN_outScalar

set_option maxHeartbeats 0 in
/-- **`portsMatchB` of `callerLN`'s SHIPPED module, from the run.** -/
theorem callerLN_portsShipped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerLN [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingPortsMatchShipped.portsMatchB_shipped
    (Tools.ShippingHierGateAny.core_hierGate_any (nDecl := 2) callerLN.machineData
    callerLN.machine_ok callerLN.machine_body callerLN_callsOk callerLN_slotLen callerLN_domB
      callerLN_insts callerLN_outTy callerLN_nomem
      hB hcore hpost entry closes)
    (callerLN_portsRaw hcore hpost entry closes hB hR0)

set_option maxHeartbeats 0 in
/-- **`hierTyped` of `callerLN`'s full-entry module, from the run**
(`core_hierTyped₁`). No check premise. -/
theorem callerLN_hierTyped {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerLN [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  Tools.ShippingOneOutConns.core_hierTyped₁ (nDecl := 2) callerLN.machineData
    callerLN.machine_ok callerLN.machine_body callerLN_callsOk callerLN_slotLen callerLN_domB
    callerLN_insts callerLN_instFields callerLN_outTy callerLN_nomem
    (callerLN_kidW hR0)
    (by
      intro k hk y hy
      rw [callerLN_entries k hk] at hy
      exact Tests.Compiler.OneOutCallerLTest.pickByteH_childTyped hR0 hy)
    (kidIns := Tests.Compiler.OneOutCallerLTest.kidIns) callerLN_callArgs
    (by
      intro k hk y hy j q hq
      rw [callerLN_entries k hk] at hy
      obtain ⟨wd, h1, -, h3⟩ := Tests.Compiler.OneOutCallerLTest.pickByteH_inWidths hR0 hy hq
      exact ⟨wd, h1, h3⟩)
    hB hcore hpost entry closes callerLN_outClean callerLN_outScalar

set_option maxHeartbeats 0 in
/-- **`designCheck` of `callerLN`'s shipped module at depth 0, from the run,
with no check premise** (`core_designCheckH` fed with `callerLN_portsShipped`). -/
theorem callerLN_designFull {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``callerLN [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``callerLN
      callerLN.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``pickByteH
      pickByteH.machineData.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingOneOutFacts.core_designCheckH (nDecl := 2) callerLN.machineData
    callerLN.machine_ok callerLN.machine_body callerLN_callsOk callerLN_slotLen callerLN_domB
    callerLN_insts callerLN_instFields callerLN_outTy callerLN_nomem
    hB hcore hpost entry closes callerLN_slots callerLN_outClean callerLN_outScalar
    (by
      intro k hk y hy
      rw [callerLN_entries k hk] at hy
      exact Tests.Compiler.OneOutCallerLTest.pickByteH_kidK hR0 hy)
    0 (callerLN_portsShipped hcore hpost entry closes hB hR0)


end Tests.Compiler.OneOutCallerLNTest

/-! ## The endpoint, by the existing command -/

set_option maxHeartbeats 0 in
#machine_design_svH_full Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN
  [Tests.Compiler.OneOutCallerLNTest.callerLN_factsH,
   Tests.Compiler.OneOutCallerLNTest.callerLN_hierTyped,
   Tests.Compiler.OneOutCallerLNTest.callerLN_designFull,
   Tests.Compiler.OneOutCallerLNTest.callerLN_outsH]

#check @Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full
#check @Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN.machine_design_svH_full_closed

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN
  let kid := ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH
  Tests.Compiler.OneOutLeafAudit.audit "ONEOUT MACHINE-LEAF" f [kid] []
    [``Tests.Compiler.OneOutCallerLNTest.callerLN_factsH,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_outsH,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_portsRaw,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_portsShipped,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_hierTyped,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_designFull]
    [``Tests.Compiler.OneOutCallerLNTest.callerLN_kidW,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_entries,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_strict,
     ``Tests.Compiler.OneOutCallerLNTest.callerLN_callArgs,
     ``Tests.Compiler.OneOutCallerLTest.pickByteH_leaf]
    false
    (Tests.Compiler.OneOutLeafAudit.scopeOf f
      "for callerLN at nDecl = 2: callerLN_callsOk, _slotLen, _domB, _insts, _instFields, _outTy, _nomem, _slots (the parent has a register), _outChars, _outScalar, _entries (every entry's callee is pickByteH), _strict (callWidthsStrict against pickByteH's layout outputs: the result binder's width), _callArgs (callArgsOk against pickByteH's declared widths); for pickByteH: the fields of pickByteH_leaf (ok, the body equation, callsOk and no late domain binder at nIn, insts = [], the slot count, output width / name / scalar conditions, gateCallsOk at nIn, lets ≠ 0, slots = [], the one output out) and its generated closing pickByteH.machine_closes"
      "hftByte (not instantiated in this file)")
