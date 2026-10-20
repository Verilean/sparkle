import Tests.Compiler.PortsMatchRawParentTest
import Tools.ShippingPortsMatchRawLeaf

/-! # `portsMatchB` of the raw full-entry module of `parent`, with no hypothesis about a module (G1, port matching)

`Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf` instantiated at
`parent` / `cnt` (`Tests/Compiler/ShippingMachineSeqTest.lean`):

* `cnt_leafKid`: the premises about the child declaration `cnt` — data by
  `decide`, its reflection `entryC` (a hypothesis), its closing
  (`cnt.machine_closes`).
* `parent_callArgs_leaf`: the argument-width data condition against
  `declWidths cnt.machineData`, by `decide`.
* `parent_portsMatch_raw_leaf`: `portsMatchB (childMap D.modules) b = true`
  for the module `b` BEFORE the optimizer, over every core run of `parent`.
  Hypotheses: the run, `hpost`, `parent`'s reflection and closing,
  `ChildBnd`, and `cnt`'s reflection. `hkidIn`, `hkidClk`, `hclkB` of
  `Tests.Compiler.PortsMatchRawParentTest.parent_portsMatch_raw` are gone.
* `cnt_declWidths`: `declWidths cnt.machineData = [1]` — `cnt`'s one
  argument port (`en : Signal dom Bool`), COMPUTED from its reflected data
  (the domain binder has no port).

Then an axiom audit (an error otherwise).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.PortsMatchRawLeafTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

/-- The premises about the leaf child `cnt`. -/
theorem cnt_leafKid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref ``cnt cnt.machineData :=
  { ok := cnt.machine_ok
    body := cnt.machine_body
    calls := by decide
    dom := by decide
    leaf := rfl
    slots := fun h0 => absurd (congrArg List.length h0) (by decide)
    ss := by decide
    outTy := by decide
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      (Tests.Compiler.KidsPassLeafTest.cnt_outs_clean o ho)
    outScalar := by decide
    entry := entryC
    closes := fun mc cc => cnt.machine_closes mc _ cc _ }

/-- The argument widths of `parent`'s calls against the widths of `cnt`'s
declared ports: a condition on the two declarations' data. -/
theorem parent_callArgs_leaf :
    Tools.ShippingPortsMatchRaw.callArgsOk parent.machineData 1
      (fun _ => Tools.ShippingPortWidthsPure.declWidths cnt.machineData) = true := by
  first
    | decide
    | decide +kernel

set_option maxHeartbeats 0 in
theorem parent_portsMatch_raw_leaf {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``parent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``parent
      parent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``parent
      parent.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b =
      true :=
  Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => cnt.machineData)
    (by
      intro k hk
      have hk' : k < 2 := hk
      cases k with
      | zero => exact cnt_leafKid entryC
      | succ k =>
        cases k with
        | zero => exact cnt_leafKid entryC
        | succ k => exact absurd hk' (by omega))
    Tests.Compiler.ChecksRawTest.parent_callWidths
    parent_callArgs_leaf
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      (Tests.Compiler.ClosedTypedTest.parent_outs_clean o ho))
    (by decide)

/-- `cnt`'s declared port widths, computed: one one-bit argument. -/
theorem cnt_declWidths : Tools.ShippingPortWidthsPure.declWidths cnt.machineData = [1] := by
  first
    | decide
    | decide +kernel

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingPortWidthsPure.inputPorts_zip_tys,
      ``Tools.ShippingPortWidthsPure.inPort_weS,
      ``Tools.ShippingPortWidthsPure.weS_clk_rst,
      ``Tools.ShippingPortWidthsPure.weS_clk_rst_filtered,
      ``Tools.ShippingLeafPorts.leaf_run_ports,
      ``Tools.ShippingLeafPorts.leaf_real_inWidths,
      ``Tools.ShippingLeafPorts.leaf_real_clk,
      ``Tools.ShippingCoreClk.core_clk,
      ``Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf,
      ``cnt_leafKid, ``parent_callArgs_leaf, ``parent_portsMatch_raw_leaf, ``cnt_declWidths] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"PORTSMATCHRAW LEAF: inputPorts_zip_tys, inPort_weS, weS_clk_rst, weS_clk_rst_filtered, leaf_run_ports, leaf_real_inWidths, leaf_real_clk, core_clk, core_portsMatch_raw_leaf, cnt_leafKid, parent_callArgs_leaf, parent_portsMatch_raw_leaf, cnt_declWidths — standard axioms only"

end Tests.Compiler.PortsMatchRawLeafTest
