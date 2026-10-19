import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tools.ShippingKidsResetSat
-- BUILT as written: ks1 (exit 0, 657 jobs; round par/kids). Writing-time guesses are marked `-- (writing-time guess, accepted by build ks1: …)`.

/-! # The four collision parents: the head's reset and children bound are satisfiable together (round par/kids)

`<p>_designClosedB` (`MemNameCollisionGateBoundTest`, head `machine_design_noPortsTB`, `Reset := Reset1`)
has among its conclusion's run hypotheses `Reset1 raw D kids` and the depth-0 children bound
`∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)`.

`<p>_kidsSat` (this file): from the CORE run (`hcore`, `hpost`, for ANY `raw` `D` the core run
returns, as `<p>_typedRun`), `MachineDefines`, the reflection `hR0` and `ChildBnd`, ONE `kids`
(`Tools.ShippingKidsResetSat.kidsZero`, every state `0`) satisfies both. The only per-parent fact is
`<p>_kidNoRegs`: every `KidT` kid has no register statement — the memory entry is the built memory
module (`memModule_noRegs`), the `.ord` entry a gate child (`noRegs_of_gate` of `gate_real_ports`,
the same reflection argument as `<p>_kidTyped`).

NOTE (interface): in `<p>_designClosedB`'s conclusion `raw` `D` are ∃-bound with only `hpost`; no
core run is exported for them, so `<p>_kidsSat` applies inside a head (where `hcore` is in scope,
as `hTyped` / `hDesign` are) or to a conclusion that also exports the core run. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)

/-! ## `collMixSame` -/

/-- Per kid, by origin: the memory entry is the built memory module, the `.ord` entry a gate
child; neither has a register statement. -/
theorem collMixSame_kidNoRegs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixSame.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixSame.machineData).shape k)
        ((collMixSame.machineData).shape.insts[k]).1 y →
      Tools.ShippingKidsResetSat.NoRegs y.1 := by
  intro k hk y hy
  obtain ⟨hn, ho⟩ := collMixSame_entry k hk
  rcases ho with ho | ho
  · rw [ho] at hy
    rw [Tools.ShippingInstTagged.KidT.mem hy (Tools.ShippingInstTagged.child?_mem false 4 8)]
    exact Tools.ShippingKidsResetSat.memModule_noRegs false 4 8
  · rw [ho, hn] at hy
    exact Tools.ShippingKidsResetSat.noRegs_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl))

set_option maxHeartbeats 4000000 in
/-- **`collMixSame`: the head's `Reset1` and depth-0 children bound hold together** for one explicit
`kids` (`kidsZero`), from the core run (any `raw` `D` it returns) and the outer premises. -/
theorem collMixSame_kidsSat {mctx : Lean.Meta.Context}
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
    ∃ kids : String → Tools.ShippingHierStateG.KT 0,
      Tools.ShippingMachineShipsHier.Reset1 raw D kids ∧
      ∀ mn iname conns gc gcwe,
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
        Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) →
        Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) 0 gc
          (kids iname) :=
  Tools.ShippingKidsResetSat.core_kidsSatMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (collMixSame_kidNoRegs hR0) hB hcore hpost entry (collMixSame_closesR hR0)

/-! ## `collMixDiff` -/

/-- Per kid, by origin: the memory entry is the built memory module, the `.ord` entry a gate
child; neither has a register statement. -/
theorem collMixDiff_kidNoRegs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixDiff.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixDiff.machineData).shape k)
        ((collMixDiff.machineData).shape.insts[k]).1 y →
      Tools.ShippingKidsResetSat.NoRegs y.1 := by
  intro k hk y hy
  rcases collMixDiff_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    rw [Tools.ShippingInstTagged.KidT.mem hy (Tools.ShippingInstTagged.child?_mem true 4 8)]
    exact Tools.ShippingKidsResetSat.memModule_noRegs true 4 8
  · rw [ho, hn] at hy
    exact Tools.ShippingKidsResetSat.noRegs_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl))

set_option maxHeartbeats 4000000 in
/-- **`collMixDiff`: the head's `Reset1` and depth-0 children bound hold together** for one explicit
`kids` (`kidsZero`), from the core run (any `raw` `D` it returns) and the outer premises. -/
theorem collMixDiff_kidsSat {mctx : Lean.Meta.Context}
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
    ∃ kids : String → Tools.ShippingHierStateG.KT 0,
      Tools.ShippingMachineShipsHier.Reset1 raw D kids ∧
      ∀ mn iname conns gc gcwe,
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
        Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) →
        Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) 0 gc
          (kids iname) :=
  Tools.ShippingKidsResetSat.core_kidsSatMT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (collMixDiff_kidNoRegs hR0) hB hcore hpost entry (collMixDiff_closesR hR0)

/-! ## `collMixArgs` -/

/-- Per kid, by origin: the memory entry is the built memory module, the `.ord` entry a gate
child; neither has a register statement. -/
theorem collMixArgs_kidNoRegs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref syncName fakeSrc.gateValue) :
    ∀ (k : Nat) (hk : k < (collMixArgs.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collMixArgs.machineData).shape k)
        ((collMixArgs.machineData).shape.insts[k]).1 y →
      Tools.ShippingKidsResetSat.NoRegs y.1 := by
  intro k hk y hy
  rcases collMixArgs_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    rw [Tools.ShippingInstTagged.KidT.mem hy (Tools.ShippingInstTagged.child?_mem false 4 8)]
    exact Tools.ShippingKidsResetSat.memModule_noRegs false 4 8
  · rw [ho, hn] at hy
    exact Tools.ShippingKidsResetSat.noRegs_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeSrc.gateBinders) hR0
        fakeSrc.gate_old fakeSrc.gate_peel fakeSrc.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl))

set_option maxHeartbeats 4000000 in
/-- **`collMixArgs`: the head's `Reset1` and depth-0 children bound hold together** for one explicit
`kids` (`kidsZero`), from the core run (any `raw` `D` it returns) and the outer premises. -/
theorem collMixArgs_kidsSat {mctx : Lean.Meta.Context}
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
    ∃ kids : String → Tools.ShippingHierStateG.KT 0,
      Tools.ShippingMachineShipsHier.Reset1 raw D kids ∧
      ∀ mn iname conns gc gcwe,
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
        Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) →
        Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) 0 gc
          (kids iname) :=
  Tools.ShippingKidsResetSat.core_kidsSatMT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (collMixArgs_kidNoRegs hR0) hB hcore hpost entry (collMixArgs_closesR hR0)

/-! ## `collWidth` -/

/-- Per kid, by origin: the memory entry is the built memory module, the `.ord` entry a gate
child; neither has a register statement. -/
theorem collWidth_kidNoRegs {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref comboName fakeN.gateValue) :
    ∀ (k : Nat) (hk : k < (collWidth.machineData).shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (originAt (collWidth.machineData).shape k)
        ((collWidth.machineData).shape.insts[k]).1 y →
      Tools.ShippingKidsResetSat.NoRegs y.1 := by
  intro k hk y hy
  rcases collWidth_entry k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    rw [Tools.ShippingInstTagged.KidT.mem hy (Tools.ShippingInstTagged.child?_mem true 4 8)]
    exact Tools.ShippingKidsResetSat.memModule_noRegs true 4 8
  · rw [ho, hn] at hy
    exact Tools.ShippingKidsResetSat.noRegs_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := fakeN.gateBinders) hR0
        fakeN.gate_old fakeN.gate_peel fakeN.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (Tools.ShippingInstTagged.KidT.real hy rfl))

set_option maxHeartbeats 4000000 in
/-- **`collWidth`: the head's `Reset1` and depth-0 children bound hold together** for one explicit
`kids` (`kidsZero`), from the core run (any `raw` `D` it returns) and the outer premises. -/
theorem collWidth_kidsSat {mctx : Lean.Meta.Context}
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
    ∃ kids : String → Tools.ShippingHierStateG.KT 0,
      Tools.ShippingMachineShipsHier.Reset1 raw D kids ∧
      ∀ mn iname conns gc gcwe,
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
        Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) →
        Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) 0 gc
          (kids iname) :=
  Tools.ShippingKidsResetSat.core_kidsSatMT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (collWidth_kidNoRegs hR0) hB hcore hpost entry (collWidth_closesR hR0)

end Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingKidsResetSat.kidsInit_sat, ``Tools.ShippingKidsResetSat.kidsZero_sat,
      ``Tools.ShippingKidsResetSat.core_noRegsMT, ``Tools.ShippingKidsResetSat.core_kidsSatMT,
      ``Tools.ShippingKidsResetSat.instAgree_of_nodup,
      ``Tools.ShippingKidsResetSat.inst_checkedOptimize_sub] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  let tn := `Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest
  for p in [`collMixSame, `collMixDiff, `collMixArgs, `collWidth] do
    Tests.Compiler.NoPortsTest.stdAxioms (tn ++ p.appendAfter "_kidNoRegs")
    Tests.Compiler.NoPortsTest.stdAxioms (tn ++ p.appendAfter "_kidsSat")

#print axioms Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixSame_kidsSat
#print axioms Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixDiff_kidsSat
#print axioms Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collMixArgs_kidsSat
#print axioms Sparkle.Tests.Compiler.MemNameCollisionKidsSatTest.collWidth_kidsSat
