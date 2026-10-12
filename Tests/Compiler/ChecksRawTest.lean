import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingChecksRaw
import Tools.ShippingChildIfaceTy
import Tools.ShippingChecksOuts
import Tools.ShippingChecksWidths
import Tools.ShippingCallWidths
import Tools.ShippingShipsHierSame
import Tools.ShippingChecksRunFacts
import Tools.ShippingShipsHierFree

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

/-! ## Conjunct 8, `instOutWidthsOk`, and the gate half of conjunct 1, on `parent`

The two per-child premises as theorems of `parent` / `cnt`:
* `parent_kidP` — `hkidP`, from `cnt`'s interface (as in `parent_outs`);
* `parent_kidW` — `hkidW`, the width agreement: a real `cnt`'s output ports
  are its layout's fields with their types (`leaf_real_outTys`), and for
  each of `parent`'s two call entries the layout field of that name has the
  width of the type of the entry's binder — ONE `decide` over the two
  declarations' data per entry. Nothing in the compiler makes this
  comparison (`Tools/ShippingChecksWidths.lean`, header).

Then `parent_widths` (`core_instOutWidthsOk`), `parent_shipsHier3`
(`shipsHierCheck` with conjuncts 1, 2, 4 left), `parent_hierGate`. -/

theorem parent_kidP {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildInv.RealChild mref cref (parent.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ Tools.ShippingInstStmtG.inPortsOf y.1, q.name ≠ p.name) ∧
        p.name ≠ "clk" ∧ p.name ≠ "rst" := by
  intro k hk y hy
  have hk' : k < 2 := hk
  have hall := (Tools.ShippingSeqChildIface.seqChild_of_real cnt.machineData cnt.machine_ok
      cnt.machine_body rfl (by decide) entryC (fun mc cc => cnt.machine_closes mc _ cc _)
      (y := y))
  cases k with
  | zero => exact (hall hy).outsIn
  | succ k =>
    cases k with
    | zero => exact (hall hy).outsIn
    | succ k => exact absurd hk' (by omega)

set_option maxHeartbeats 0 in
theorem parent_kidW {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildInv.RealChild mref cref (parent.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = parent.machineData.shape.instFields.getD k "" →
        (parent.machineData.shape.binders[1 + k]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some p.ty.bitWidth := by
  intro k hk y hy p hp hpn
  have hk' : k < 2 := hk
  have hout := fun (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) =>
    (Tools.ShippingChildIfaceTy.leaf_real_outTys cnt.machineData cnt.machine_ok cnt.machine_body
      rfl (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide) entryC
      (fun mc cc => cnt.machine_closes mc _ cc _) h).outputs
  cases k with
  | zero =>
    rw [hout hy] at hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hp
    exact (by decide : ∀ o ∈ cnt.machineData.shape.layout.outs,
      o.name = parent.machineData.shape.instFields.getD 0 "" →
      (parent.machineData.shape.binders[1 + 0]?).map
        (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth)
      o ho hpn
  | succ k =>
    cases k with
    | zero =>
      rw [hout hy] at hp
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hp
      exact (by decide : ∀ o ∈ cnt.machineData.shape.layout.outs,
        o.name = parent.machineData.shape.instFields.getD (0 + 1) "" →
        (parent.machineData.shape.binders[1 + (0 + 1)]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth)
        o ho hpn
    | succ k => exact absurd hk' (by omega)

set_option maxHeartbeats 0 in
theorem parent_widths {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingHierOpen.instOutWidthsOk (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true :=
  Tools.ShippingChecksWidths.core_instOutWidthsOk (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) (parent_kidP entryC) (parent_kidW entryC)
    hB hcore hpost entry closes

set_option maxHeartbeats 0 in
theorem parent_hierGate {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Sparkle.IR.RefineCheck.hierGate b = true :=
  Tools.ShippingChecksWidths.core_hierGate (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) hB hcore hpost entry closes

set_option maxHeartbeats 0 in
theorem parent_shipsHier3 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    (hflat : Sparkle.IR.RefineCheck.refineCheck
      (Sparkle.IR.HierCheck.openFlat b (Sparkle.IR.HierCheck.openIns b)
        (Sparkle.IR.HierCheck.openOuts b))
      (Sparkle.IR.HierCheck.openFlat b (Sparkle.IR.HierCheck.openIns b)
        (Sparkle.IR.HierCheck.openOuts b)) = true)
    (hwfO : Tools.ShippingHierOpen.linkedWF (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b).body = true)
    (hndO : (Tools.ShippingHierState.instNames
      (Sparkle.IR.OptCheck.checkedOptimize b).body).Nodup) :
    Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules)
      b = true :=
  Tools.ShippingChecksWidths.core_shipsHier_rest3F (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) (parent_kidP entryC) (parent_kidW entryC)
    hB hcore hpost entry closes hflat hwfO hndO

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingTransitionPortTys.transitionPortTys_of_run,
      ``Tools.ShippingInstWidthsParts.instOutWidthsOk_of,
      ``Tools.ShippingInstWidthsParts.callStmtG_outWireF,
      ``Tools.ShippingInstWidthsParts.hierGate_of,
      ``Tools.ShippingChecksWidths.core_callPorts,
      ``Tools.ShippingChecksWidths.core_instOutWidthsOk,
      ``Tools.ShippingChecksWidths.core_shipsHier_rest3,
      ``Tools.ShippingChecksWidths.core_hierGate,
      ``Tools.ShippingChecksWidths.core_shipsHier_rest3F,
      ``parent_kidP, ``parent_kidW, ``parent_widths, ``parent_hierGate, ``parent_shipsHier3] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CHECKSWIDTHS: transitionPortTys_of_run, instOutWidthsOk_of, callStmtG_outWireF, hierGate_of, core_callPorts, core_instOutWidthsOk, core_shipsHier_rest3, core_hierGate, core_shipsHier_rest3F, parent_kidP, parent_kidW, parent_widths, parent_hierGate, parent_shipsHier3 — standard axioms only"

/-! ## The width agreement as a condition on the data (Finding A)

`parent_callWidths`: `callWidthsOk` of `parent` against `cnt`'s layout — ONE
`decide` over the two declarations' reflected data, no run.
`parent_kidW_data`: `hkidW` from it and `cnt`'s output ports
(`hkidW_of_data`, `leaf_real_outTys`). -/

theorem parent_callWidths :
    Tools.ShippingCallWidths.callWidthsOk parent.machineData 1
      (fun _ => cnt.machineData.shape.layout.outs) = true := by decide

set_option maxHeartbeats 0 in
theorem parent_kidW_data {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    ∀ (k : Nat) (hk : k < parent.machineData.shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildInv.RealChild mref cref (parent.machineData.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = parent.machineData.shape.instFields.getD k "" →
        (parent.machineData.shape.binders[1 + k]?).map
          (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some p.ty.bitWidth :=
  Tools.ShippingCallWidths.hkidW_of_data parent_callWidths (by
    intro k hk y hy
    have hk' : k < 2 := hk
    have hall := fun (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) =>
      Tools.ShippingChildIfaceTy.leaf_real_outTys cnt.machineData cnt.machine_ok cnt.machine_body
        rfl (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide)
        entryC (fun mc cc => cnt.machine_closes mc _ cc _) h
    cases k with
    | zero => exact hall hy
    | succ k =>
      cases k with
      | zero => exact hall hy
      | succ k => exact absurd hk' (by omega))

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingCallWidths.hkidW_of_data,
      ``Tools.ShippingShipsHierSame.machine_ships_hierC_same,
      ``parent_callWidths, ``parent_kidW_data] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CHECKSDATA: hkidW_of_data, machine_ships_hierC_same, parent_callWidths, parent_kidW_data — standard axioms only"

/-! ## Without the bundled checker (branch `fix/opt-fallback`)

`parent_runFacts`: the `facts` argument of `machine_ships_hierC_free` for
`parent` — the run's facts of the full entry's module, from the core run,
`parent`'s and `cnt`'s reflections and the data (`core_runFacts`; no
`shipsHierCheck`, no `hierBinds`, no post-pass fact).
`parent_shipped`: the SHIPPED module of `parent` is linked-well-formed, has
distinct instance names and the full entry's inputs — conjuncts 2 and 4 of
`shipsHierCheck` and `checkedOptimize_inputs`, with no check premise. -/

set_option maxHeartbeats 0 in
theorem parent_runFacts {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingChecksRunFacts.core_runFacts (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) (parent_kidP entryC) (parent_kidW_data entryC)
    hB hcore hpost entry closes

theorem parent_shipped {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingHierOpen.linkedWF (Tools.ShippingMachineLinked.childMap D.modules)
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      (Tools.ShippingHierState.instNames (Sparkle.IR.OptCheck.checkedOptimize b).body).Nodup ∧
      (Sparkle.IR.OptCheck.checkedOptimize b).inputs = b.inputs :=
  Tools.ShippingChecksRunFacts.core_shipped_facts
    (parent_runFacts hcore hpost entry closes hB entryC)

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingGuardsSound.linkedWFX_sound,
      ``Tools.ShippingGuardsSound.deinline_guards,
      ``Tools.ShippingGuardsSound.checkedOptimize_facts,
      ``Tools.ShippingShipsHierFree.machine_ships_hierC_free,
      ``Tools.ShippingChecksRunFacts.core_runFacts,
      ``parent_runFacts, ``parent_shipped] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CHECKSFREE: linkedWFX_sound, deinline_guards, checkedOptimize_facts, machine_ships_hierC_free, core_runFacts, parent_runFacts, parent_shipped — standard axioms only"

end Tests.Compiler.ChecksRawTest
