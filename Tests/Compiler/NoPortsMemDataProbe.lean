import Tests.Compiler.ShippingDesignSVMemTest
import Tools.ShippingMachineSeqCommandR

/-! # Memory-only parents: the reader's data and the derived-boundary endpoint — a PROBE, logs only (G1, unit U4, round par/b-13)

TARGET-BUILT ONLY, not for `Tests/AllTests.lean`: the second command, where
it succeeds, leaves `memCounter.machine_composedTR(A)`,
`memCounter.machine_ships_hierR` and `memCounter.machine_design_svR0` in the
environment of this module.

Nothing here is asserted and nothing is a result. It replaces three cells
the census (`docs/parallel/A-remaining.md` §1, rows 9–13) marks "not read"
for `memCounter`, `twoMems`, `mixedMems`, `memWide`, `syncNarrow`:

1. the reader's data: `nDecl`, the call entries, `instFields`, whether the
   `Signal.loop` registers are `layout.slots` (the check-free chain of
   `Tools/ShippingMemKidFacts.lean` asks `slots ≠ []`), `loops`;
2. which of the constants the chain builds on exist (`machine_ok`,
   `machine_body`, `machine_ships_hier`, `machine_ships_hierR`,
   `machine_design_sv0`, `machine_design_svR0`, `machine_closes`);
3. for `memCounter` only: whether `#machine_design_svR0` goes through on a
   parent whose calls are ALL memories (READ:
   `Tools/ShippingMachineSeqCommandR.lean` 36–38 computes the sequential
   children as the callees that are not memories and handles an empty list
   nowhere explicitly; `generateSeqChild` is not called then; the reflection
   premise would be the empty conjunction).

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for f in [``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems,
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide,
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow] do
    try
      let r ← Tools.ShippingMachineCommand.readMachine f
      Lean.logInfo m!"NOPORTS MEM PROBE DATA {f}: nDecl={r.nDecl}, binders={r.shape.binders.length}, call entries {r.shape.insts.map (·.1)}, argument lets {r.shape.insts.map (·.2.1)}, instFields={r.shape.instFields}, slots={r.shape.layout.slots.length}, lets={r.shape.layout.lets}, outputs {r.shape.layout.outs.map (·.name)}, loops={r.shape.loops.length}"
    catch e =>
      Lean.logInfo m!"NOPORTS MEM PROBE DATA {f}: readMachine failed: {e.toMessageData}"
    let env ← Lean.getEnv
    let mut have_ : List Lean.Name := []
    let mut lack : List Lean.Name := []
    for s in [`machineData, `machine_ok, `machine_body, `machine_closes, `machine_ships_hier,
        `machine_ships_hierR, `machine_design_sv0, `machine_design_svR0] do
      if env.contains (f ++ s) then have_ := have_ ++ [s] else lack := lack ++ [s]
    Lean.logInfo m!"NOPORTS MEM PROBE CONSTANTS {f}: present {have_}; absent {lack}"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
  try
    let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
      Tools.ShippingMachineSeqCommand.generateDesignR0 f
    let ty := (← Lean.getConstInfo name).type
    let mut ms : List Lean.Name := []
    for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
        ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingMachineShipsHier.kidsMem,
        ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSVBack.outsCheck,
        ``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildBnd] do
      if (ty.find? (·.isConstOf k)).isSome then ms := ms ++ [k]
    Lean.logInfo m!"NOPORTS MEM PROBE R0 {f}: GENERATED {name}; its statement mentions {ms}"
  catch e =>
    Lean.logInfo m!"NOPORTS MEM PROBE R0 {f}: REFUSED — {e.toMessageData}"
