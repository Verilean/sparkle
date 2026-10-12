import Tests.Compiler.NoDesignTest
import Tests.Compiler.KidsPassLeafTest
import Tools.ShippingNoKidsCommand

/-! # The depth SV endpoint without the children's check (round par/a-1)

With the print guard in `mergeChecked`
(`Sparkle.IR.RefineCheck.mergeChecked_print`), the children's check of a
parent whose children are leaf machines with a register follows from the
children's runs.

* By hand, at `parent` / `cnt`: `cnt_kidK_reg` (`kidCheck C n y.1 = true` at
  every depth, for every `RealChild` of `cnt` — NO `hmergePrint` premise)
  and `parent_kidsPass_reg` (`hkids` of `core_designCheck_run` for `parent`
  with only runs, reflections and the boundary as premises).
* Generated: `#machine_no_kids f n` on `parent` and `chained`
  (`Tests/Compiler/ShippingMachineSeqTest.lean`): `f.machine_designK1`
  (`designCheck` of the shipped module from the core run and the connection
  widths), `f.machine_design_noKidsNR1` and its `_closed` form:
  `∃ raw D, … ∧ (portsMatchB … → Bnd → …)`.

`#machine_goal_gap_of` on the closed forms logs the `GOALGAP` lines. Then,
as errors otherwise: standard axioms only; no statement mentions
`kidsPass`, `designCheck`, `shipsHierCheck`, `hierCheck`, `outsCheck` or
`kidsMaskedN`; the gap theorem of each has EXACTLY ONE gap hypothesis,
`gap_portsMatchB`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.NoKidsTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
/-- The children's check of every real `cnt` module, no premise on its merge. -/
theorem cnt_kidK_reg {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true :=
  Tools.ShippingLeafTyped.leaf_real_kidK_reg (nDecl := cnt.machineData.nIn) cnt.machineData
    cnt.machine_ok cnt.machine_body (by decide) (by decide) rfl
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) entry
    (fun mc cc => cnt.machine_closes mc _ cc _)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      (Tests.Compiler.KidsPassLeafTest.cnt_outs_clean o ho))
    (by decide) h

set_option maxHeartbeats 0 in
/-- **`hkids` of `core_designCheck_run` for `parent`**, at every depth: runs,
reflections and the boundary only. -/
theorem parent_kidsPass_reg {mctx : Lean.Meta.Context}
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
      cnt.machineData.shape)
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
        cnt_kidK_reg entryC h
      cases k with
      | zero => exact hall hy
      | succ k =>
        cases k with
        | zero => exact hall hy
        | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes n

end Tests.Compiler.NoKidsTest

set_option maxHeartbeats 0 in
#machine_no_kids Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent 1

set_option maxHeartbeats 0 in
#machine_no_kids Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained 1

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_designK1
#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noKidsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noKidsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_noKidsNR1_closed

namespace Tests.Compiler.NoKidsTest
open Lean Meta Elab Command

run_cmd liftTermElabM do
  let mut lines : Array String := #[]
  for n in [``Sparkle.IR.RefineCheck.mergeChecked_print,
      ``Sparkle.IR.RefineCheck.mergeChecked_print_cases,
      ``Sparkle.IR.RefineCheck.mergeChecked_masks,
      ``Sparkle.IR.RefineCheck.mergeChecked_nonAssign,
      ``Tools.ShippingLeafTyped.leaf_run_typedIn,
      ``Tools.ShippingLeafTyped.leaf_real_kidK_reg,
      ``Tools.ShippingKidsPassLeaf.core_kidsPass_leaf,
      ``Tools.ShippingNoKids.machine_design_noKids,
      ``cnt_kidK_reg, ``parent_kidsPass_reg] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  -- `parent_kidsPass_reg` has no premise about the merge or the print guard
  let ci ← getConstInfo ``parent_kidsPass_reg
  for c in [``Sparkle.IR.PrintGuard.printOk] do
    if (ci.type.find? (·.isConstOf c)).isSome then
      throwError "parent_kidsPass_reg: the statement mentions {c}"
  for f in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained] do
    let made := [f ++ `machine_designK1,
      f ++ `machine_design_noKidsNR1, f ++ `machine_design_noKidsNR1_closed,
      f ++ `machine_design_noKidsNR1_closed_gap]
    for n in made do
      unless (← getEnv).contains n do throwError "{n}: not generated"
      for ax in ← Lean.collectAxioms n do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{n} uses a non-standard axiom: {ax}"
    for n in [f ++ `machine_design_noKidsNR1,
        f ++ `machine_design_noKidsNR1_closed,
        f ++ `machine_design_noKidsNR1_closed_gap] do
      let ci ← getConstInfo n
      for c in [``Tools.ShippingDesignSV.kidsPass,
          ``Tools.ShippingDesignSV.designCheck,
          ``Tools.ShippingHierPremisesBase.shipsHierCheck,
          ``Tools.ShippingHierPremisesBase.hierCheck,
          ``Tools.ShippingDesignSVBack.outsCheck,
          ``Tools.ShippingMachineShipsDepth.kidsMaskedN] do
        if (ci.type.find? (·.isConstOf c)).isSome then
          throwError "{n}: the statement mentions {c}"
    let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames
      (f ++ `machine_design_noKidsNR1_closed_gap)
    unless gaps == ["gap_portsMatchB"] do
      throwError "{f}: the gap hypotheses are {gaps}, expected [gap_portsMatchB]"
    lines := lines.push s!"{f}: gap hypotheses {gaps}"
  logInfo m!"NOKIDS TEST: parent and chained — machine_designK1, machine_design_noKidsNR1, its _closed form and its gap theorem on standard axioms; no statement mentions kidsPass, designCheck, shipsHierCheck, hierCheck, outsCheck or kidsMaskedN; the one gap hypothesis is gap_portsMatchB; cnt_kidK_reg and parent_kidsPass_reg (by hand) on standard axioms, no print-guard premise; {lines}"

end Tests.Compiler.NoKidsTest
