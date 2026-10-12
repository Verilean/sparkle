import Tests.Compiler.NoPortsMemOnlyCounterTest

/-! # A memory-only parent's endpoint under `MachineClosesAt` — a PROBE, logs only (G1, unit U4, round par/b-14)

TARGET-BUILT ONLY, not for `Tests/AllTests.lean`: where the attempt
succeeds it leaves `memCounter.machine_design_noPortsR0` in the environment
of this module. Nothing here is asserted and nothing is a result.

`memCounter.machine_design_noPorts0` (`NoPortsMemOnlyCounterTest`) keeps the
old endpoint's closing premise `MachineCloses` — every world, every logger
(`Tools/ShippingMachineEntry.lean` 2279–2284). The form the other check-free
endpoints ask is `MachineClosesAt` (`Tools/ShippingChildRun.lean` 444–449).
`#machine_design_svR0 memCounter` REFUSES ("no sequential child", MEASURED,
run 20261013-055644-b13b-alltests).

The attempt (`generateM0 … (atForm := true)`): the wired endpoint is the `RA`
twin of `memCounter.machine_sound`'s head
(`machine_traceL_of_loop_causalRA`, `Tools/ShippingMachineSeqLinkedR.lean`
25–85: `MachineClosesAt` and `ChildBnd` in place of `MachineCloses`),
forgotten to `MachineTraceLB` (`MachineTraceLBX.toLB`); the composed theorem
is `machine_linkedT_mem` on it with the ten data arguments of the existing
`memCounter.machine_composedT`, read off its proof term. No new general
theorem is involved. This is READ, not measured: whether the `RA` head takes
the same data arguments as the head of `machine_sound` for a memory-only
parent is what the log line says.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
  let saved ← Lean.getEnv
  try
    let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
      Tests.Compiler.NoPortsMemOnly.generateM0 f
        ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_runFacts
        ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_outsG0
        ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_kidsMemG
        ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_designP0
        (atForm := true)
    let ty := (← Lean.getConstInfo name).type
    let mut ms : List Lean.Name := []
    for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
        ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingMachineShipsHier.kidsMem,
        ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSVBack.outsCheck,
        ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildInv.MachineClosesAt,
        ``Tools.ShippingChildInv.ChildBnd] do
      if (ty.find? (·.isConstOf k)).isSome then ms := ms ++ [k]
    let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines name
    Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
    Lean.logInfo m!"NOPORTS MEMONLY AT PROBE {f}: GENERATED {name}; its statement mentions {ms}; {bad.size} premise(s) NOT ALLOWED by the goal-gap classifier (logged above). PROBE ONLY — not in AllTests, nothing claimed"
  catch e =>
    Lean.setEnv saved
    Lean.logInfo m!"NOPORTS MEMONLY AT PROBE {f}: REFUSED — {e.toMessageData}"
