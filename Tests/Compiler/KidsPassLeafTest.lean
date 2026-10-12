import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingKidsPassLeaf

/-! # The children's check of `parent`, from the leaf child `cnt` (G1, round optfb-7)

`Tools.ShippingLeafTyped` and `Tools.ShippingKidsPassLeaf` instantiated at
`parent` / `cnt` (`Tests/Compiler/ShippingMachineSeqTest.lean`), the data
premises by `decide`:

* `cnt_outs_clean`: the output port names of `cnt`, character by character;
* `cnt_typedIn`: over every `RealChild` of `cnt`, its module is a typed
  module or that module's checked merge, and its ports are resolved by the
  emitter's width map (`PortsIn`) either way;
* `cnt_kidK`: `kidCheck C n y.1 = true` at every depth, under `hmergePrint`
  (the merged module passes the print guard — NOT derived);
* `parent_kidsPass`: `hkids` of `core_designCheck_run` for `parent` at every
  depth, with ONE premise that is not a run, a reflection or the boundary:

      hmergePrint : ∀ y, RealChild mref cref ``cnt y →
        ∀ m0, y.1 = mergeChecked m0 → y.1 = m0 ∨ printOk y.1 = true

Then an axiom audit (an error otherwise).

`cnt`'s `nDecl` is `cnt.machineData.nIn` (a machine without calls:
`callsOk` asks `nDecl + insts.length = nIn`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.KidsPassLeafTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

/-- The output port names of `cnt`, character by character. -/
theorem cnt_outs_clean :
    ∀ o ∈ cnt.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true := by
  first
    | decide
    | decide +kernel

set_option maxHeartbeats 0 in
theorem cnt_typedIn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) :
    ∃ m0 : Sparkle.IR.AST.Module,
      (y.1 = m0 ∨ y.1 = Sparkle.IR.RefineCheck.mergeChecked m0) ∧
      Tools.ShippingTextTyped.TypedIn m0 ∧
      m0.body.all Sparkle.IR.OptCheck.seqStmtOk = true ∧
      Tools.ShippingLeafTyped.PortsIn y.1 ∧
      y.1.body.all Sparkle.IR.OptCheck.seqStmtOk = true :=
  Tools.ShippingLeafTyped.leaf_real_typedIn (nDecl := cnt.machineData.nIn) cnt.machineData
    cnt.machine_ok cnt.machine_body (by decide) (by decide) rfl (by decide) (by decide) entry
    (fun mc cc => cnt.machine_closes mc _ cc _)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (cnt_outs_clean o ho))
    (by decide) h

set_option maxHeartbeats 0 in
theorem cnt_kidK {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y)
    (hmergePrint : ∀ m0 : Sparkle.IR.AST.Module, y.1 = Sparkle.IR.RefineCheck.mergeChecked m0 →
      y.1 = m0 ∨ Sparkle.IR.PrintGuard.printOk y.1 = true) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true :=
  Tools.ShippingLeafTyped.leaf_real_kidK (nDecl := cnt.machineData.nIn) cnt.machineData
    cnt.machine_ok cnt.machine_body (by decide) (by decide) rfl (by decide) (by decide) entry
    (fun mc cc => cnt.machine_closes mc _ cc _)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (cnt_outs_clean o ho))
    (by decide) h hmergePrint

set_option maxHeartbeats 0 in
/-- **`hkids` of `core_designCheck_run` for `parent`**, at every depth. -/
theorem parent_kidsPass {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    -- NOT derived: a merged `cnt` module passes the print guard
    (hmergePrint : ∀ y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design,
      Tools.ShippingChildInv.RealChild mref cref ``cnt y →
      ∀ m0 : Sparkle.IR.AST.Module, y.1 = Sparkle.IR.RefineCheck.mergeChecked m0 →
        y.1 = m0 ∨ Sparkle.IR.PrintGuard.printOk y.1 = true)
    (n : Nat) :
    Tools.ShippingDesignSV.kidsPass (Tools.ShippingMachineLinked.childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (Tools.ShippingMachineLinked.childMap D.modules) n)
      (Sparkle.IR.OptCheck.checkedOptimize b).body = true :=
  Tools.ShippingKidsPassLeaf.core_kidsPass_leaf (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (by
      intro k hk y hy
      have hk' : k < 2 := hk
      have hall := fun (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) =>
        cnt_kidK entryC h (hmergePrint y h)
      cases k with
      | zero => exact hall hy
      | succ k =>
        cases k with
        | zero => exact hall hy
        | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes n

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingLeafTyped.linkedWF_seq,
      ``Tools.ShippingLeafTyped.leafCheck_of_text,
      ``Tools.ShippingLeafTyped.kidCheck_leaf_of_text,
      ``Tools.ShippingLeafTyped.PortsIn.wof_output,
      ``Tools.ShippingLeafTyped.leaf_run_typedIn,
      ``Tools.ShippingLeafTyped.leaf_real_typedIn,
      ``Tools.ShippingLeafTyped.leaf_real_portsIn,
      ``Tools.ShippingLeafTyped.leaf_real_kidK,
      ``Tools.ShippingLeafTyped.leaf_real_kidK_id,
      ``Tools.ShippingKidsPassLeaf.core_kidsPass_leaf,
      ``cnt_outs_clean, ``cnt_typedIn, ``cnt_kidK, ``parent_kidsPass] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"KIDSPASSLEAF: linkedWF_seq, leafCheck_of_text, kidCheck_leaf_of_text, PortsIn.wof_output, leaf_run_typedIn, leaf_real_typedIn, leaf_real_portsIn, leaf_real_kidK, leaf_real_kidK_id, core_kidsPass_leaf, cnt_outs_clean, cnt_typedIn, cnt_kidK, parent_kidsPass — standard axioms only"

end Tests.Compiler.KidsPassLeafTest
