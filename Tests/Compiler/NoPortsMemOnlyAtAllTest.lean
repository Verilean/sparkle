import Tests.Compiler.ShippingDesignSVMemTest
import Tools.ShippingMemOnlyAtAll

/-! # The all-worlds closing of the five memory-only parents: its counter-world, instantiated (G1, unit U4, round par/b-15)

`Tools.ShippingMemOnlyAtAll.not_machineCloses_of_synthNone` instantiated at
the reflected shape of `memCounter` (the data of all five memory-only
parents `memCounter`, `syncNarrow`, `twoMems`, `mixedMems`, `memWide` is
logged; the general theorem asks `insts ≠ []` only, which the first command
asserts of each): ONE successful run of the harness whose transition `closeLets` accepts
and whose end world reads no child synthesis contradicts
`MachineCloses f f.machineData.shape` — the closing premise of the built
`f.machine_design_sv0` and `f.machine_design_noPorts0`.

What this is NOT: a proof of `¬ MachineCloses f …`. The existence of such a
run is not derivable in the model (no existence statement for runs of the
harness); see the header of `Tools/ShippingMemOnlyAtAll.lean`. The theorems
below only need `insts ≠ []` of each shape.

No endpoint changes here. Independent of the `NoPortsMemOnlyAt<Decl>Test`
files (it imports none of them).

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for f in [``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems,
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide] do
    let rf ← Tools.ShippingMachineCommand.readMachine f
    let fe := rf.shape.insts.map (·.1)
    Lean.logInfo m!"NOPORTS MEMONLY ALL-WORLDS DATA {f}: call entries {fe}, instFields={rf.shape.instFields}, lets={rf.shape.layout.lets}, slots={rf.shape.layout.slots.length}"
    if fe.isEmpty then throwError "{f}: no call entry — the counter-world theorem does not apply"
    let dataN := f ++ `machineData
    unless (← Lean.getEnv).contains dataN do throwError "{dataN}: not in the imports"

namespace Tests.Compiler.NoPortsMemOnlyAtAllTest
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry

/-- **`memCounter`: the all-worlds closing against one run that ends where
the child synthesis reference reads `none`.** -/
theorem memCounter_notAll {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {logProf : String → IO Unit} {w w1 w2 : Void IO.RealWorld}
    {t t' : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.binders
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.body)
      mctx mref cctx cref w (t, d) w1)
    (hcl : Sparkle.IR.Machine.closeLets
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape.layout.lets
      t = some t')
    (hget : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w1 none w2) :
    ¬ MachineCloses mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape :=
  Tools.ShippingMemOnlyAtAll.not_machineCloses_of_synthNone
    (shape := (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData).shape)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) hr hcl hget

end Tests.Compiler.NoPortsMemOnlyAtAllTest

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingMemOnlyAtAll.closeInstsGM_none_of_synthNone,
      ``Tools.ShippingMemOnlyAtAll.closeInstsM_none_of_synthNone,
      ``Tools.ShippingMemOnlyAtAll.closeCalls_none_of_synthNone,
      ``Tools.ShippingMemOnlyAtAll.not_machineCloses_of_synthNone,
      ``Tests.Compiler.NoPortsMemOnlyAtAllTest.memCounter_notAll] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  -- the statement is conditional: it has the three run hypotheses as binders
  let ty := (← Lean.getConstInfo ``Tools.ShippingMemOnlyAtAll.not_machineCloses_of_synthNone).type
  unless (ty.find? (·.isConstOf ``Tools.ShippingMachineEntry.MachineCloses)).isSome do
    throwError "not_machineCloses_of_synthNone: does not mention MachineCloses"
  unless (ty.find? (·.isConstOf ``Sparkle.Compiler.Elab.sparkleChildSynth)).isSome do
    throwError "not_machineCloses_of_synthNone: does not mention the child synthesis reference"
  Lean.logInfo m!"NOPORTS MEMONLY ALL-WORLDS AUDIT: on standard axioms, MachineCloses of a shape with calls (memory-only shapes included) is contradicted by ONE harness run accepted by closeLets that ends in a world where sparkleChildSynth reads none (not_machineCloses_of_synthNone; instantiated at memCounter). CONDITIONAL: the existence of such a run is NOT proved (not derivable in the model) — so ¬ MachineCloses is not a theorem; what is recorded is that the all-worlds closing premise of f.machine_design_sv0 / f.machine_design_noPorts0 cannot be discharged, and that no endpoint changes. The memory entries themselves read nothing (pure md); the read that fails is the closing's first statement."
