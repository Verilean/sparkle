import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tools.ShippingWireNamesRun
import Tools.ShippingNoPortsTypedB

/-! # The four collision parents with NO added start-state hypothesis (round o-bo)

`<p>_designClosedT` (`MemNameCollisionGateTypedTest` / `…TypedAllTest`, head `machine_design_noPortsT`) carry
ONE added run hypothesis in their conclusions: `BoundOff (declWidth b) outputs st0`. It is NOT derivable from
the other start-state hypotheses (counterexample `st0 "clk" = 1`; `docs/parallel/O-origin-integration.md`).

`<p>_designClosedB` (this file, head `Tools.ShippingNoPortsTyped.machine_design_noPortsTB`):
* the input ports need no start-state bound, because `seedIn` overwrites them (`fitX_of_runTypedS`);
* the bound off outputs and inputs is DERIVED from the conclusion's existing
  `Bounded (weS (checkedOptimize b)) st0` (`boundOffI_of_bounded`, `weS_checkedOptimize_le`);
* the head's name-facts hypothesis `hNames` (`b`'s wire names distinct, all names sanitize-stable) is
  discharged from the core run by `<p>_names` (`Tools.ShippingWireNamesRun.wireNames_runMT`), with data
  conditions decided on the concrete `MachineData`.

So the conclusions' run hypotheses are those of the untyped head `machine_design_noPorts`. The outer premises
(the run, `MachineDefines`, `EntryDefines`) and the nested `ChildBnd` are unchanged. -/

namespace Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
open Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
open Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
open Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest

set_option maxHeartbeats 4000000 in
/-- **The name facts of `collMixSame`'s full-entry module, from the core run** (`wireNames_runMT`). -/
theorem collMixSame_names {mctx : Lean.Meta.Context}
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
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  Tools.ShippingWireNamesRun.wireNames_runMT (nDecl := 3)
    collMixSame.machineData collMixSame.machine_ok collMixSame.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixSame_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixSame_outChars o ho))
    (by first | decide | decide +kernel)

set_option maxHeartbeats 4000000 in
/-- **The name facts of `collMixDiff`'s full-entry module, from the core run** (`wireNames_runMT`). -/
theorem collMixDiff_names {mctx : Lean.Meta.Context}
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
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  Tools.ShippingWireNamesRun.wireNames_runMT (nDecl := 3)
    collMixDiff.machineData collMixDiff.machine_ok collMixDiff.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixDiff_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixDiff_outChars o ho))
    (by first | decide | decide +kernel)

set_option maxHeartbeats 4000000 in
/-- **The name facts of `collMixArgs`'s full-entry module, from the core run** (`wireNames_runMT`). -/
theorem collMixArgs_names {mctx : Lean.Meta.Context}
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
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  Tools.ShippingWireNamesRun.wireNames_runMT (nDecl := 3)
    collMixArgs.machineData collMixArgs.machine_ok collMixArgs.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collMixArgs_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collMixArgs_outChars o ho))
    (by first | decide | decide +kernel)

set_option maxHeartbeats 4000000 in
/-- **The name facts of `collWidth`'s full-entry module, from the core run** (`wireNames_runMT`). -/
theorem collWidth_names {mctx : Lean.Meta.Context}
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
    (b.wires.map (·.name)).Nodup ∧
      ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
  Tools.ShippingWireNamesRun.wireNames_runMT (nDecl := 3)
    collWidth.machineData collWidth.machine_ok collWidth.machine_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    hB hcore hpost entry (collWidth_closesR hR0)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (collWidth_outChars o ho))
    (by first | decide | decide +kernel)

end Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest

/-! ## The endpoints, by the generator with the TB head (the kernel checks the results) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := `Sparkle.Tests.Compiler.MemNameCollisionGateCertTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  -- (parent, child, source, value equation, namespace of runFacts/outsG0/designP0, of typedRun, of closesR)
  for (p, cC, src, eqN, fN, tN, rN) in [(`collMixSame, `syncName, `fakeSrc, `syncGate_value, cn, yn, ns),
      (`collMixDiff, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collMixArgs, `syncName, `fakeSrc, `syncGate_value, an, an, an),
      (`collWidth, `comboName, `fakeN, `comboGate_value, an, an, an)] do
    let n ← Tools.ShippingGateTypedCommand.generateTop
      { parent := ns ++ p, name := bn ++ p.appendAfter "_designClosedB",
        childConst := ns ++ cC, gateValue := ns ++ src ++ `gateValue,
        valueEq? := some (ns ++ eqN),
        runFacts := fN ++ p.appendAfter "_runFacts", outsG0 := fN ++ p.appendAfter "_outsG0",
        typedRun := tN ++ p.appendAfter "_typedRun", designP0 := fN ++ p.appendAfter "_designP0",
        closesR := rN ++ p.appendAfter "_closesR",
        head := ``Tools.ShippingNoPortsTyped.machine_design_noPortsTB,
        names? := some (bn ++ p.appendAfter "_names") }
    Lean.logInfo m!"GATEBOUND [{n}]: head machine_design_noPortsTB; hNames by {p}_names (wireNames_runMT); NO added start-state hypothesis (BoundOff refused in the statement)"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let bn := `Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest
  let cn := `Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest
  let yn := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedTest
  let an := `Sparkle.Tests.Compiler.MemNameCollisionGateTypedAllTest
  for n in [``Tools.ShippingNoPortsTyped.machine_design_noPortsTB,
      ``Tools.ShippingNoPortsTypedI.fitX_of_runTypedS, ``Tools.ShippingNoPortsTypedI.weS_checkedOptimize_le,
      ``Tools.ShippingWireNamesRun.wireNames_runMT, ``Tools.ShippingWireNamesRun.boundOffI_runMT] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  let bindersOf (t : Lean.Expr) : Lean.MetaM (Array String) :=
    Lean.Meta.forallTelescope t fun xs _ => do
      let mut out : Array String := #[]
      for x in xs do
        let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp ty then out := out.push (toString (← Lean.Meta.ppExpr ty))
      return out
  let inner (t : Lean.Expr) := Lean.Meta.forallTelescope t fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  for (p, oldN) in [(`collMixSame, yn), (`collMixDiff, an), (`collMixArgs, an), (`collWidth, an)] do
    let fin := bn ++ p.appendAfter "_designClosedB"
    let old := oldN ++ p.appendAfter "_designClosedT"
    Tests.Compiler.NoPortsTest.stdAxioms (bn ++ p.appendAfter "_names")
    Tests.Compiler.NoPortsTest.stdAxioms fin
    let finT := (← Lean.getConstInfo fin).type
    let oldT := (← Lean.getConstInfo old).type
    for k in Tests.Compiler.NoPortsTest.checkers ++
        [``Tools.ShippingHierTyped.BoundOff, ``Tools.ShippingKidsMixedC.kidsMixedC,
         ``Tools.ShippingKidsMixedC.combOk, ``Tools.ShippingMachineShipsHier.kidsMixed,
         ``Tools.ShippingKidsTyped.TypedRun, ``Tools.ShippingChildInv.MachineClosesAt,
         ``Tools.ShippingInstTagged.TagsAgree] do
      if (finT.find? (·.isConstOf k)).isSome then throwError "{fin}: the statement mentions {k}"
    unless (oldT.find? (·.isConstOf ``Tools.ShippingHierTyped.BoundOff)).isSome do
      throwError "{old}: does not mention BoundOff (the comparison is wrong)"
    let bs ← bindersOf finT
    let ia ← inner finT
    unless bs.size == 3 do throwError "{fin}: {bs.size} Prop binders, expected 3"
    unless ia.size == 1 do throwError "{fin}: {ia.size} antecedents under the existentials, expected 1"
    let cnt := Sparkle.Tests.Compiler.MemNameCollisionGateClosedTest.countApps
      ``Tools.ShippingInlineSoundness.EntryDefines 6 finT
    unless cnt == 1 do throwError "{fin}: {cnt} EntryDefines occurrences, expected 1"
    Lean.logInfo m!"GATEBOUND PREMISES {fin}: {bs.size} Prop binders {bs}; {ia.size} antecedents under the existentials {ia.map (·.1)}; no BoundOff (was in {old})"

#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixSame_designClosedB
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixDiff_designClosedB
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collMixArgs_designClosedB
#print axioms Sparkle.Tests.Compiler.MemNameCollisionGateBoundTest.collWidth_designClosedB
