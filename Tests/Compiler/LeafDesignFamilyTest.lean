import Lean.Elab.Command
import Tests.Compiler.LeafDesignCntTest
import Tests.Compiler.LeafEntryFamilyTest
import Tools.ShippingLeafDesignCommand

/-! # `#machine_leaf_design` on the family of leaf register machines (round par/b-27)

`Tools/ShippingLeafDesignCommand.lean`: for a machine declaration without
calls and with a register slot whose `f.machine_ships_wired` exists, the
command adds `f.machine_design_leaf0` — the design-level endpoint in the
parents' depth-0 shape, `∃ raw, (b = … ∨ b = …) ∧ (ChildBnd mref cref w →
… DesignSV (childMap design.modules) 0 (checkedOptimize b) …)`, with binders
exactly the run and `MachineDefines f`.

`cnt` is `Tests/Compiler/LeafDesignCntTest.lean` (by hand, then the compare
path). Here, in order:

(i) `GENERATED` for the six leaf register machines of
    `Tests/Compiler/LeafEntryFamilyTest.lean`:

| declaration | shape |
|---|---|
| `acc` | `circuit do`, one 8-bit register, structure result with a `BitVec 8` and a `Bool` field, any domain |
| `pe` | `circuit do`, two 32-bit registers, three 32-bit inputs, a multiplication, structure result |
| `twoHW` | `circuit do`, TWO registers of different kinds (8-bit, `Bool`), two shared `let`s, structure result |
| `toggle` | `circuit do`, a `Bool` register and a `Bool` OUTPUT, the concrete default domain |
| `loopPair` | a `Signal.loop` over a pair: two 32-bit registers, the tuple state as one packed 64-bit port |
| `toggleL` | a `Signal.loop` with one `Bool` register as the whole value, any domain |

    each followed by `#machine_goal_gap_of` on its endpoint (the parents'
    gap tool);
(ii) the audit of each — the gap theorem has NO `gap_…` hypothesis; the
    parents' premise listing (`Tests.Compiler.NoPortsTest.premiseLines`): 0
    NOT ALLOWED; no checker constant; the command's own audit
    (`Tools.ShippingLeafDesignCommand.audit`: exactly the run,
    `MachineDefines f` and `ChildBnd`; none of `simpleBody` / `seqCheck` /
    `seqNames` / `MachineCloses` / `InvW` / `printOk` / `isAssign`; standard
    axioms);
(iii) `REFUSED` — the refusals of the leaf-entry family, by the SAME scan —
    for `pickByteH` (slotless), `parent` (has calls), `memCounter` (memory)
    and `plain` (not a machine), and that the refusals left nothing.

## Imports and names

`f.machine_leafKid`, `f.machine_closes` and `f.machine_ships_wired` of the
six are in the imports (`LeafEntryFamilyTest` generated or imported them);
nothing of that is generated here. Generated here: `machine_design_leaf0`
and `machine_design_leaf0_gap` of the six. `cnt.machine_design_leaf0`,
`…_regen`, `…_gap` are `LeafDesignCntTest`'s.

## SCOPE (binding for any report)

Per declaration: ONE declaration as an entry, depth 0, no call;
`DesignSV` of the module list over the returned design's child map — not the
SV string, not `#sim`; data conditions decided for that declaration; the
run, the reflection and `ChildBnd` stay premises; a compiler with the two
guards of `Sparkle/IR/RefineCheck.lean`. Seven declarations (with `cnt`),
not the register leaves of the census.

WRITTEN, NOT BUILT. -/
namespace Tests.Compiler.LeafDesignFamilyTest

/-- The declarations of (i). -/
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
      [f ++ `machineData, f ++ `machine_closes, f ++ `machine_ships_wired,
        f ++ `machine_leafKid, f ++ `machine_ships_leafC, f ++ `machine_design_leaf0,
        f ++ `machine_design_leaf0_regen, f ++ `machine_design_leaf0_gap]
    let there : List Lean.Name := names.filter fun n => env.contains n
    lines := lines.push s!"LEAFDESIGN FAMILY IMPORTS {f}: in the environment {there}"
  for l in lines do Lean.logInfo l
  unless env.contains (c ++ `machine_design_leaf0) do
    throwError "{c}.machine_design_leaf0: not in the imports (LeafDesignCntTest)"
  for f in generated do
    for s in [`machine_design_leaf0, `machine_design_leaf0_regen, `machine_design_leaf0_gap] do
      if env.contains (f ++ s) then
        throwError "{f ++ s}: exists already (another file generates it: NAME CLASH)"
    for s in [`machine_closes, `machine_ships_wired, `machine_leafKid] do
      unless env.contains (f ++ s) do
        throwError "{f ++ s}: not in the imports (LeafEntryFamilyTest) — it would be generated here and could clash in Tests.AllTests"

/-! ## (i) GENERATED, and the parents' gap tool on each -/

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_design_leaf0

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.MultiInstance.pe "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.MultiInstance.pe.machine_design_leaf0

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW.machine_design_leaf0

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle.machine_design_leaf0

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair.machine_design_leaf0

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machine_design_leaf0

/-! ## (ii) The audit of each, by the parents' tools and by the command's -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let mut summary : Array String := #[]
  for f in generated do
    let leaf := f ++ `machine_design_leaf0
    let gap := f ++ `machine_design_leaf0_gap
    for n in [leaf, gap] do
      unless env.contains n do throwError "{n}: not generated"
      Tests.Compiler.NoPortsTest.stdAxioms n
      let ci ← Lean.getConstInfo n
      for k in Tests.Compiler.NoPortsTest.checkers do
        if (ci.type.find? (·.isConstOf k)).isSome then
          throwError "{n}: the statement mentions {k}"
    let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
    unless gaps.isEmpty do
      throwError "{f}: the gap hypotheses are {gaps}, expected none"
    let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines leaf
    Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
    unless bad.isEmpty do
      throwError "{leaf}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
    Tools.ShippingLeafDesignCommand.audit f
    summary := summary.push
      s!"{f}: no gap hypothesis, {lines.size} binders and antecedents listed, 0 not allowed"
  Lean.logInfo m!"LEAFDESIGN FAMILY AUDIT: {summary}"

/-! ## (iii) REFUSED, with the reason; nothing is left -/

#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH "REFUSED"

#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent "REFUSED"

#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "REFUSED"

#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain "REFUSED"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  for f in refusedDecls do
    for s in [`machine_design_leaf0, `machine_design_leaf0_regen, `machine_design_leaf0_gap,
        `machine_leafKid] do
      if env.contains (f ++ s) then
        throwError "{f ++ s}: left in the environment by a REFUSED run"
  let mut made : List Lean.Name := []
  for f in generated do
    unless env.contains (f ++ `machine_design_leaf0) do
      throwError "{f}.machine_design_leaf0: not in the environment after (i)"
    made := made ++ [f ++ `machine_design_leaf0]
  Lean.logInfo m!"LEAFDESIGN FAMILY: GENERATED and audited {made} — each ∃ raw, (b = … ∨ b = …) ∧ (ChildBnd → … DesignSV (childMap design.modules) 0 (checkedOptimize b) …: a closed run showing the source exists, and every closed run from the same seeding and states shows it), binders exactly the run and MachineDefines of the declaration; audited by the parents' tools (#machine_goal_gap_of: no gap hypothesis; NoPortsTest.premiseLines: 0 NOT ALLOWED; no checker constant) and by the command's audit; standard axioms; REFUSED with a reason and nothing left: {refusedDecls}. With cnt (LeafDesignCntTest: by hand, and REBUILT isDefEq): seven declarations. SCOPE: each as an entry, depth 0, no call; data conditions decided per declaration (conditions, not reductions); the run, the reflection and ChildBnd stay premises; a compiler with the two guards of Sparkle/IR/RefineCheck.lean; DesignSV of the module list — not the SV string, not #sim; NOT a statement about the other register leaves of the census"

end Tests.Compiler.LeafDesignFamilyTest
