import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingChecksRaw
import Tools.ShippingChildIfaceTy
import Tools.ShippingChecksOuts

/-! # The raw-module facts on a real declaration (G1)

`Tools.ShippingChecksRaw.core_raw_facts` and
`Tools.ShippingChildIfaceTy.leaf_real_outTys`, instantiated at `parent` and
its leaf child `cnt` (`Tests/Compiler/ShippingMachineSeqTest.lean`), the
data premises by `decide` — the same terms the generated
`parent.machine_outs1` uses for the hypotheses these theorems share with
`core_outsCheck_all`:

* `parent_raw`: over ANY core run of `parent` at the child boundary, with
  its reflection and closing, the full entry's module has the reset input,
  distinct instance names, and passes the self-read test on the core run's
  design — three conjuncts of `shipsHierCheck`;
* `cnt_outTys`: a real `cnt` child's module has the layout's output ports
  with their types.

Then an audit: these two, and the three theorems they come from, use the
standard axioms only (an error otherwise). -/
namespace Tests.Compiler.ChecksRawTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
theorem parent_raw {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingChecksRaw.core_raw_facts (nDecl := 1) parent.machineData parent.machine_ok
    parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) hB hcore hpost entry closes

set_option maxHeartbeats 0 in
theorem cnt_outTys {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) :
    Tools.ShippingChildIfaceTy.ChildOutTys cnt.machineData.shape.layout.outs y.1 :=
  Tools.ShippingChildIfaceTy.leaf_real_outTys cnt.machineData cnt.machine_ok cnt.machine_body rfl
    (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide) entry
    (fun mc cc => cnt.machine_closes mc _ cc _) h

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingChecksRaw.core_raw_facts, ``Tools.ShippingChecksRaw.core_shipsHier_rest,
      ``Tools.ShippingChildIfaceTy.leaf_real_outTys, ``parent_raw, ``cnt_outTys] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CHECKSRAW: core_raw_facts, core_shipsHier_rest, leaf_real_outTys, parent_raw, cnt_outTys — standard axioms only"

/-! ## Conjunct 6, `outsExtracted`, on `parent`

`Tools.ShippingChecksOuts.core_outsExtracted` at `parent`: the per-child fact
`hkidP` (the child's output ports are apart from its argument ports, `clk`
and `rst`) is the leaf child `cnt`'s interface (`seqChild_of_real`, field
`outsIn`), from `cnt`'s reflection `entryC` — the premise the closing
generators already take of a child. `parent_shipsHier4`: `shipsHierCheck`
with the four conjuncts left (1, 2, 4, 8). -/

set_option maxHeartbeats 0 in
theorem parent_outs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingHierPremisesBase.outsExtracted (Tools.ShippingMachineLinked.childMap D.modules)
      b = true :=
  Tools.ShippingChecksOuts.core_outsExtracted (nDecl := 1) parent.machineData parent.machine_ok
    parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (by
      intro k hk y hy
      -- `parent` has two entries of its one call, both of `cnt`
      have hk' : k < 2 := hk
      have hall := (Tools.ShippingSeqChildIface.seqChild_of_real cnt.machineData cnt.machine_ok
          cnt.machine_body rfl (by decide) entryC (fun mc cc => cnt.machine_closes mc _ cc _)
          (y := y))
      cases k with
      | zero => exact (hall hy).outsIn
      | succ k =>
        cases k with
        | zero => exact (hall hy).outsIn
        | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes

set_option maxHeartbeats 0 in
theorem parent_shipsHier4 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
      cnt.machineData.shape)
    (hb : Sparkle.IR.RefineCheck.hierBinds b = true)
    (hwfO : Tools.ShippingHierOpen.linkedWF (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b).body = true)
    (hndO : (Tools.ShippingHierState.instNames (Sparkle.IR.OptCheck.checkedOptimize b).body).Nodup)
    (hwid : Tools.ShippingHierOpen.instOutWidthsOk (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true) :
    Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules)
      b = true :=
  Tools.ShippingChecksOuts.core_shipsHier_rest4 (nDecl := 1) parent.machineData parent.machine_ok
    parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (by
      intro k hk y hy
      -- `parent` has two entries of its one call, both of `cnt`
      have hk' : k < 2 := hk
      have hall := (Tools.ShippingSeqChildIface.seqChild_of_real cnt.machineData cnt.machine_ok
          cnt.machine_body rfl (by decide) entryC (fun mc cc => cnt.machine_closes mc _ cc _)
          (y := y))
      cases k with
      | zero => exact (hall hy).outsIn
      | succ k =>
        cases k with
        | zero => exact (hall hy).outsIn
        | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes hb hwfO hndO hwid

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingClosedPorts.closedBody_regs,
      ``Tools.ShippingClosedPorts.closedPorts_of_run,
      ``Tools.ShippingOutsExtractedParts.outsExtracted_of_parts,
      ``Tools.ShippingOutsExtractedParts.callStmtG_outWire,
      ``Tools.ShippingChecksOuts.core_outsExtracted,
      ``Tools.ShippingChecksOuts.core_shipsHier_rest4, ``parent_outs, ``parent_shipsHier4] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CHECKSOUTS: closedBody_regs, closedPorts_of_run, outsExtracted_of_parts, callStmtG_outWire, core_outsExtracted, core_shipsHier_rest4, parent_outs, parent_shipsHier4 — standard axioms only"

end Tests.Compiler.ChecksRawTest
