import Tests.Compiler.NoPortsMemGenFamilyTest

/-! # `#machine_no_ports_mem`: the output facts FROM THE READER against the previous data path, on ONE tree (round par/r-2)

WRITTEN, NOT BUILT.

## TARGET-ONLY — never in `Tests/AllTests.lean`

It imports `Tests.Compiler.NoPortsMemGenFamilyTest` (target-only: it creates
the names the hand tests own). NEVER co-import with
`Tests.Compiler.NoPortsMemGenOldNamesTest` (both add `…_regen` of the same
names).

## What is compared

`NoPortsMemGenFamilyTest` generated, with the NEW path (par/r-2: no
`noPortsMem_outTy` / `_outScalar` decided; `noPortsMem_dataR :
MemOnlyDataR …`; the four run theorems by `memOnly_*_of_reader`, i.e. the
two output facts from `Tools.ShippingReaderOutsInv.outTy_of_core` /
`outScalar_of_core`; the closing by `machineClosesAt_of_memOnlyDataR_names`),
the endpoints of the memory-only parents. Here the PREVIOUS data path
(`#machine_no_ports_mem_olddata_try f "REBUILT"`) runs on the five
untransported ones — `memCounter`, `syncNarrow`, `memWide`, `twoMems`,
`mixedMems` — in the SAME environment. It is a different generator path from
the one that made the existing names (never a generator compared with
itself). Every name the two paths share exists already, so the command takes
its compare path on each: the theorem is elaborated again under `…_regen`
(kernel-checked) and its statement must be `isDefEq` the existing one, or
the command fails (`emit` / `addOrCompare`). The names only the old path has
(`outTy`, `outScalar`, `data`) are GENERATED now.

Asserted after the five runs (an error otherwise), for each `f`:

* every one of the 20 shared names `n` (`sharedNames`) and `n_regen` exist,
  the two statements are `isDefEq` (kernel `isDefEq` of the two TYPES), and
  `n_regen` is on standard axioms;
* the four run theorems: the NEW proof applies `memOnly_*_of_reader` and not
  `memOnly_*`; the OLD (`…_regen`) applies `memOnly_*` and not
  `memOnly_*_of_reader`;
* the closing: new `machineClosesAt_of_memOnlyDataR_names`, old
  `machineClosesAt_of_memOnlyData_names`;
* `noPortsMem_dataR` exists (new) and `noPortsMem_data`, `_outTy`,
  `_outScalar` exist (old, generated now), all on standard axioms;
* acceptance: the number of compared pairs is `5 × 20 = 100` and non-zero.

NOT compared: the proof terms beyond the constants above. `withMemory`
(transported) is not run here: add a line to extend. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_olddata_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "REBUILT"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_olddata_try Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow "REBUILT"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_olddata_try Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide "REBUILT"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_olddata_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems "REBUILT"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_olddata_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems "REBUILT"

namespace Tests.Compiler.NoPortsMemGenOldDataTest
open Lean Meta

/-- The names both paths generate (statements must agree). -/
def sharedNames (f : Name) : List Name :=
  (["entry", "calls", "slots", "domB", "callWidths", "callArgs", "outChars",
    "runFacts", "outsG0", "kidsMemG", "designP0",
    "alias", "argsN", "field", "argsNd", "outHead", "closeData", "closes"].map fun s =>
      f ++ Name.mkSimple s!"noPortsMem_{s}") ++
  [f ++ `machine_design_noPortsR0, f ++ `machine_design_noPortsR0_closed]

def direct (n : Name) : MetaM (Array Name) := do
  match (← getEnv).find? n with
  | some (.thmInfo ti) => return ti.value.getUsedConstants
  | _ => throwError "{n}: not a theorem"

/-- The comparison on one declaration; returns the number of compared pairs. -/
def compare (f : Name) : MetaM Nat := do
  let env ← getEnv
  let mut count := 0
  for n in sharedNames f do
    let r := Tools.ShippingNoPortsKidsCommand.regenName n
    unless env.contains n do throwError "{n}: missing (the family test is not in the imports)"
    unless env.contains r do throwError "{r}: missing — the previous data path did not rebuild {n}"
    Tests.Compiler.NoPortsTest.stdAxioms r
    unless ← isDefEq (← getConstInfo n).type (← getConstInfo r).type do
      throwError "{r}: its statement is not that of {n}"
    count := count + 1
  -- the four run theorems: the proofs differ as designed
  let pairs : List (String × Name × Name) :=
    [("runFacts", ``Tools.ShippingReaderOutsMemOnly.memOnly_runFacts_of_reader,
        ``Tools.ShippingMemOnly.memOnly_runFacts),
     ("outsG0", ``Tools.ShippingReaderOutsMemOnly.memOnly_outsCheck_of_reader,
        ``Tools.ShippingMemOnly.memOnly_outsCheck),
     ("kidsMemG", ``Tools.ShippingReaderOutsMemOnly.memOnly_kidsMem_of_reader,
        ``Tools.ShippingMemOnly.memOnly_kidsMem),
     ("designP0", ``Tools.ShippingReaderOutsMemOnly.memOnly_designCheck_of_reader,
        ``Tools.ShippingMemOnly.memOnly_designCheck),
     ("closes", ``Tools.ShippingReaderMemOnlyCloses.machineClosesAt_of_memOnlyDataR_names,
        ``Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names)]
  for (s, kNew, kOld) in pairs do
    let n := f ++ Name.mkSimple s!"noPortsMem_{s}"
    let r := Tools.ShippingNoPortsKidsCommand.regenName n
    let uNew ← direct n
    let uOld ← direct r
    unless uNew.contains kNew && !uNew.contains kOld do
      throwError "{n}: expected the NEW path's {kNew} (and not {kOld}): {uNew}"
    unless uOld.contains kOld && !uOld.contains kNew do
      throwError "{r}: expected the PREVIOUS path's {kOld} (and not {kNew}): {uOld}"
  -- the data lemmas of each path
  for s in ["dataR", "data", "outTy", "outScalar"] do
    let n := f ++ Name.mkSimple s!"noPortsMem_{s}"
    unless env.contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  logInfo m!"NOPORTS MEM OLDDATA COMPARE {f}: the previous data path rebuilt {count} shared names as …_regen; each rebuilt statement isDefEq the one the new path generated (kernel isDefEq of the types); the run theorems apply memOnly_*_of_reader (new) / memOnly_* (old), the closing machineClosesAt_of_memOnlyDataR_names (new) / machineClosesAt_of_memOnlyData_names (old); {f}.noPortsMem_outTy / _outScalar / _data were generated by the OLD path only (the new path has {f}.noPortsMem_dataR)."
  return count

end Tests.Compiler.NoPortsMemGenOldDataTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let fs : List Lean.Name :=
    [``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
     ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow,
     ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide,
     ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems,
     ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems]
  let mut total := 0
  for f in fs do
    total := total + (← Tests.Compiler.NoPortsMemGenOldDataTest.compare f)
  unless total == fs.length * 20 && total != 0 do
    throwError "NOPORTS MEM OLDDATA COMPARE: {total} pairs compared, expected {fs.length * 20}"
  -- the general theorems the new path rests on
  for n in [``Tools.ShippingReaderOutsInv.outTy_of_core,
      ``Tools.ShippingReaderOutsInv.outScalar_of_core,
      ``Tools.ShippingReaderMemOnlyCloses.machineClosesAt_of_memOnlyDataR_names] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  Lean.logInfo m!"NOPORTS MEM OLDDATA COMPARE: {total} pairs over {fs.length} declarations, all isDefEq; per declaration the new path decides 2 output facts fewer (outTy, outScalar)."
