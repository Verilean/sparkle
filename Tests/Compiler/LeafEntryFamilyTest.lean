import Lean.Elab.Command
import Tests.Compiler.LeafEntryCntClosedTest
import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.NoPortsSlotlessEngineOnceTest
import Tests.Compiler.NoPortsLoopParentTest
import Tests.Compiler.ShippingMachineCommandTest
import Tests.Compiler.ShippingMachineLoopTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingMachineMemLinkedTest
import Tools.ShippingLeafEntryCommand

/-! # `#machine_leaf_entry` on a family of leaf register machines (round par/a-32)

`Tools/ShippingLeafEntryCommand.lean`: for a machine declaration without
calls and with a register slot whose `f.machine_ships_wired` exists, the
command adds `f.machine_ships_leafC` — the conclusion of
`f.machine_ships_wired` at the emitter's own width map, with premises
exactly the run, `MachineDefines f` and `ChildBnd`.

## What this file runs, in order

(i) the COMPARE path on `cnt`: `cnt.machine_ships_leafC` exists (by hand,
    `Tests/Compiler/LeafEntryCntClosedTest.lean`); the command rebuilds it,
    adds `cnt.machine_ships_leafC_regen` and requires the two statements to
    be `isDefEq` — expected outcome `REBUILT`;
(ii) `GENERATED` for six leaf register machines of different shapes:

| declaration | defined in | shape |
|---|---|---|
| `acc` | `ShippingChildBoundaryTest` 34 | `circuit do`, one 8-bit register, structure result with a `BitVec 8` and a `Bool` field, any domain |
| `pe` | `MultiInstanceTest` 34 | `circuit do`, two 32-bit registers, three 32-bit inputs, a multiplication, structure result |
| `twoHW` | `ShippingMachineEntryTest` 58 | `circuit do`, TWO registers of different kinds (8-bit, `Bool`), two shared `let`s, structure result |
| `toggle` | `ShippingMachineCommandTest` 38 | `circuit do`, a `Bool` register and a `Bool` OUTPUT (one port `out`), the concrete default domain |
| `loopPair` | `ShippingMachineLoopTest` 97 | a `Signal.loop` over a pair: two WIDE (32-bit) registers, the whole tuple state as one packed 64-bit port |
| `toggleL` | `ShippingMachineSeqLoopTest` 22 | a `Signal.loop` with one `Bool` register as the whole value, any domain |

    each followed by the audit `Tools.ShippingLeafEntryCommand.audit` (the
    audit of `LeafEntryCntClosedTest` §3: the premise listing through
    `Tools.ShippingFinalGoalCommand.allowed`, exactly three proposition
    binders, 0 NOT ALLOWED, none of `simpleBody` / `seqCheck` / `seqNames` /
    `MachineCloses` / `InvW` / `printOk` / `isAssign`, standard axioms);
(iii) `REFUSED` for `pickByteH` (slotless), `parent` (has calls),
    `memCounter` (memory) and `plain` (not a machine), and that the refusals
    left nothing.

`toggleL` and `loopPair` are loop-built endpoints
(`machine_trace_of_loop` / `_of_regs`). They are in the command's scope by
reading (the command's header: the leaf-entry theorems read `LeafKid` and
`f.machine_ships_wired`, not the endpoint's head); `toggleL.machine_leafKid`
is BUILT (`Tests/Compiler/NoPortsLoopParentTest.lean`). Whether
`toggleL.machine_ships_wired` / `loopPair.machine_ships_wired` exist is NOT
known before the build: the `LEAFENTRY DATA` line of each says so, and if
one is missing the outcome is `REFUSED` with that reason and this file fails
at that line (expected class `GENERATED`).

Every outcome line is preceded by `LEAFENTRY DATA` with the reader's data
(logged by the command before the outcome).

## Imports and names

`cnt.machine_leafKid` (`NoPortsTest`), `acc.machine_leafKid`
(`NoPortsTwoTest`), `pe.machine_leafKid` (`NoPortsSlotlessEngineOnceTest`)
and `toggleL.machine_leafKid` (`NoPortsLoopParentTest`) are IMPORTED — a
second module generating them would clash in `Tests.AllTests`. Generated
here: `machine_leafKid` of `twoHW`, `toggle`, `loopPair` (no other file
makes them, `grep`), `machine_ships_leafC` of the six, and
`cnt.machine_ships_leafC_regen`.

## SCOPE (binding for any report)

Per declaration: ONE module (`MachineShips` at the emitter's own width map) —
not `DesignSV`, not the SV string, not `#sim`; data conditions decided for
that declaration; the run, the reflection and `ChildBnd` stay premises; a
compiler with the two guards of `Sparkle/IR/RefineCheck.lean`. Seven
declarations, not the ~80 of the census.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.LeafEntryFamilyTest

/-- The declarations of (ii). -/
def generated : List Lean.Name :=
  [``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc,
    ``Sparkle.Tests.Compiler.MultiInstance.pe,
    ``Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW,
    ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle,
    ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair,
    ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL]

/-- The declarations of (iii). -/
def refusedDecls : List Lean.Name :=
  [``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH,
    ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
    ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain]

/-! ## 0. What the imports give: LOGGED first, then asserted -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let mut lines : Array String := #[]
  for f in [c] ++ generated ++ refusedDecls do
    let names : List Lean.Name :=
      [f ++ `machineData, f ++ `machine_sound, f ++ `machine_closes, f ++ `machine_ships_wired,
        f ++ `machine_ships_comb, f ++ `machine_leafKid, f ++ `machine_ships_leafC,
        f ++ `machine_ships_leafC_regen]
    let there : List Lean.Name := names.filter fun n => env.contains n
    lines := lines.push s!"LEAFFAMILY IMPORTS {f}: in the environment {there}"
  for l in lines do Lean.logInfo l
  unless env.contains (c ++ `machine_ships_leafC) do
    throwError "{c}.machine_ships_leafC: not in the imports (the compare path needs the hand-built theorem of LeafEntryCntClosedTest)"
  if env.contains (c ++ `machine_ships_leafC_regen) then
    throwError "{c}.machine_ships_leafC_regen: exists already"
  for f in generated do
    if env.contains (f ++ `machine_ships_leafC) then
      throwError "{f}.machine_ships_leafC: exists already (another file generates it: NAME CLASH)"

/-! ## (i) The compare path on `cnt` -/

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt "REBUILT"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let old := c ++ `machine_ships_leafC
  let regen := c ++ `machine_ships_leafC_regen
  let env ← Lean.getEnv
  unless env.contains regen do
    throwError "{regen}: not added by the compare path"
  let tOld := (← Lean.getConstInfo old).type
  let tNew := (← Lean.getConstInfo regen).type
  let same ← Lean.Meta.isDefEq tOld tNew
  let syntactic : Bool := tOld == tNew
  Lean.logInfo m!"LEAFFAMILY COMPARE {c}: {regen} (the generator's term) against {old} (the hand-built term of LeafEntryCntClosedTest): isDefEq {same}; syntactically equal {syntactic}"
  unless same do
    throwError "{regen}: its statement is not isDefEq that of {old}"
  -- the generator's statement passes the generator's own checks, and so
  -- does the hand-built one
  discard <| Tools.ShippingLeafEntryCommand.checkStatement c regen tNew
  Tools.ShippingLeafEntryCommand.audit c
  for ax in ← Lean.collectAxioms regen do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{regen} uses a non-standard axiom: {ax}"

/-! ## (ii) GENERATED, each audited -/

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tools.ShippingLeafEntryCommand.audit ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.MultiInstance.pe "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tools.ShippingLeafEntryCommand.audit ``Sparkle.Tests.Compiler.MultiInstance.pe

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tools.ShippingLeafEntryCommand.audit ``Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tools.ShippingLeafEntryCommand.audit ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tools.ShippingLeafEntryCommand.audit ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair

set_option maxHeartbeats 0 in
#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tools.ShippingLeafEntryCommand.audit ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL

/-! ## (iii) REFUSED, with the reason; nothing is left -/

#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH "REFUSED"

#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent "REFUSED"

#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "REFUSED"

#machine_leaf_entry_try Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain "REFUSED"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  for f in refusedDecls do
    for s in [`machine_ships_leafC, `machine_ships_leafC_regen, `machine_leafKid] do
      if env.contains (f ++ s) then
        throwError "{f ++ s}: left in the environment by a REFUSED run"
  let mut made : List Lean.Name := []
  for f in generated do
    unless env.contains (f ++ `machine_ships_leafC) do
      throwError "{f}.machine_ships_leafC: not in the environment after (ii)"
    made := made ++ [f ++ `machine_ships_leafC]
  Lean.logInfo m!"LEAFFAMILY: REBUILT (isDefEq, proof kept as _regen) for cnt; GENERATED and audited {made} — each the conclusion of its machine_ships_wired at the emitter's own width map wofOf (checkedOptimize b), premises exactly the run, MachineDefines of the declaration and ChildBnd, 0 NOT ALLOWED, none of simpleBody / seqCheck / seqNames / MachineCloses / InvW / printOk / isAssign, standard axioms; REFUSED with a reason and nothing left: {refusedDecls}. SCOPE: seven declarations, each as an entry, ONE module each; data conditions decided per declaration (conditions, not reductions); the run, the reflection and ChildBnd stay premises; a compiler with the two guards of Sparkle/IR/RefineCheck.lean; not DesignSV, not the SV string, not #sim; NOT a statement about the other leaf machines of the census"

end Tests.Compiler.LeafEntryFamilyTest
