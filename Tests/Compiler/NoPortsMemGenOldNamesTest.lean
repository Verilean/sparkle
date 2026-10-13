import Tests.Compiler.NoPortsMemGenFamilyTest

/-! # `#machine_no_ports_mem`: the new closing path against the previous one, on ONE tree (round par/b-30)

WRITTEN, NOT BUILT.

## TARGET-ONLY — never in `Tests/AllTests.lean`

It imports `Tests.Compiler.NoPortsMemGenFamilyTest` (target-only: it creates
the names the hand tests own).

## What is compared

`NoPortsMemGenFamilyTest` generated, with the NEW path
(`f.noPortsMem_closes` by
`Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names`, no name
lemma), the endpoints of the six memory-only parents. Here the PREVIOUS path
(`#machine_no_ports_mem_oldnames_try f "REBUILT"`) runs on two of them —
`memCounter` (one placeholder) and `mixedMems` (two) — in the SAME
environment. Every name the two paths share exists already, so the command
takes its compare path on each: the theorem is elaborated again under
`…_regen` (kernel-checked) and its statement must be `isDefEq` the existing
one, or the command fails (`emit` / `addOrCompare`).

Asserted after the two runs (an error otherwise), for each `f`:

* `f.noPortsMem_closes_regen` (the previous path's closing) exists, on
  standard axioms; its statement `isDefEq` that of `f.noPortsMem_closes`;
  its proof term applies `machineClosesAt_of_memOnlyData` (WITH name
  hypotheses) while `f.noPortsMem_closes` applies `…_names`;
* `f.machine_design_noPortsR0_regen` and `…_closed_regen` exist and their
  statements are `isDefEq` those of the endpoints (kernel `isDefEq` of the
  two TYPES — not a hash, not a printed text);
* the previous path's name lemmas were generated now (they were absent
  before: the family audit asserts that).

NOT compared: the PROOF terms (they differ by design in `noPortsMem_closes`;
the endpoints' proofs both go through `f.noPortsMem_closes`, the existing
one). The other four parents (`syncNarrow`, `memWide`, `twoMems`,
`withMemory`): add a line each to extend. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_oldnames_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "REBUILT"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_oldnames_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems "REBUILT"

namespace Tests.Compiler.NoPortsMemGenOldNamesTest
open Lean Meta

def direct (n : Name) : MetaM (Array Name) := do
  match (← getEnv).find? n with
  | some (.thmInfo ti) => return ti.value.getUsedConstants
  | _ => throwError "{n}: not a theorem"

def compare (f : Name) (nMems : Nat) : MetaM Unit := do
  let env ← getEnv
  let pairs := ["noPortsMem_closes", "machine_design_noPortsR0",
    "machine_design_noPortsR0_closed"].map fun s =>
      (f ++ Name.mkSimple s, f ++ Name.mkSimple (s ++ "_regen"))
  for (n, r) in pairs do
    unless env.contains n do throwError "{n}: missing (the family test is not in the imports)"
    unless env.contains r do throwError "{r}: missing — the previous path did not rebuild {n}"
    Tests.Compiler.NoPortsTest.stdAxioms r
    unless ← isDefEq (← getConstInfo n).type (← getConstInfo r).type do
      throwError "{r}: its statement is not that of {n}"
  let cl := f ++ `noPortsMem_closes
  let clOld := f ++ `noPortsMem_closes_regen
  let uNew ← direct cl
  let uOld ← direct clOld
  let genNew := ``Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
  let genOld := ``Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
  unless uNew.contains genNew && !uNew.contains genOld do
    throwError "{cl}: expected the closing without name hypotheses: {uNew}"
  unless uOld.contains genOld && !uOld.contains genNew do
    throwError "{clOld}: expected the closing WITH name hypotheses: {uOld}"
  let olds := Tests.Compiler.NoPortsMemGenFamilyTest.oldNameLemmas f nMems
  for n in olds do
    unless env.contains n do throwError "{n}: the previous path did not generate it"
    Tests.Compiler.NoPortsTest.stdAxioms n
  logInfo m!"NOPORTS MEM OLDNAMES COMPARE {f}: the previous closing path rebuilt {pairs.map (·.1)} as …_regen; each rebuilt statement isDefEq the one the new path generated (kernel isDefEq of the types); {cl} applies {genNew}, {clOld} applies {genOld} with the per-declaration name lemmas {olds}. The endpoints' NAMES and TYPES are the same in the two paths; only the proof of {cl} differs."

end Tests.Compiler.NoPortsMemGenOldNamesTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemGenOldNamesTest.compare
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter 1
  Tests.Compiler.NoPortsMemGenOldNamesTest.compare
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems 2
