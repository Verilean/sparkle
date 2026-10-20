import Tests.Compiler.NoPortsMemSeqGenNewTest
import Tests.Compiler.NoPortsMemSeqGenNew2Test

/-! # `#machine_no_ports_memseq`: the output facts FROM THE READER against the previous data path, on ONE tree (round par/r-5)

WRITTEN, NOT BUILT.

## TARGET-ONLY — never in `Tests/AllTests.lean`

It adds `…_regen` of every generated name of `seqTwoMem` and `seqAccSync`.
NEVER co-import with `Tests.Compiler.NoPortsMemSeqGenOldNamesTest` (it adds
`…_regen` of the same names of `seqTwoMem`: the second compare path would
stop at "exists already").

## What is compared

`NoPortsMemSeqGenNewTest` / `NoPortsMemSeqGenNew2Test` (both in `AllTests`)
generated the endpoints of `seqTwoMem` and `seqAccSync` with the DEFAULT path
(par/r-5: no `noPortsMemSeq_outTy` / `_outScalar` decided; the four run
theorems pass `Tools.ShippingReaderOutsInv.outTy_of_core hcore entry` and —
`designP0` — `outScalar_of_core hcore entry`). Here the PREVIOUS data path
(`#machine_no_ports_memseq_olddata_try f "REBUILT"`) runs on both in the SAME
environment — a different generator path from the one that made the
existing names. Every shared name exists, so the command takes its compare
path on each: the declaration is elaborated again under `…_regen`
(kernel-checked) and its statement (a table: its value) must be `isDefEq` the
existing one, or the command fails. The two names only the old path has
(`outTy`, `outScalar`) are GENERATED now.

Asserted after the two runs (an error otherwise), per declaration:

* every shared name `n` (the lemma list of the declaration's own audit in
  `NoPortsMemSeqGenNewTest` / `…New2Test`, minus `outTy` / `outScalar`, plus
  the two endpoints) and `n_regen` exist, `n_regen` is on standard axioms and
  the two TYPES are `isDefEq` (`Lean.Meta.isDefEq`, as
  `NoPortsMemGenOldDataTest`); how many are also syntactically equal (`==`)
  is logged;
* the four run theorems: the NEW proof's direct constants contain
  `outTy_of_core` and not `f.noPortsMemSeq_outTy`; the OLD (`…_regen`) the
  reverse; `designP0` likewise for `outScalar_of_core` /
  `f.noPortsMemSeq_outScalar`;
* `f.noPortsMemSeq_outTy` / `_outScalar` exist now (old path), standard
  axioms, and have NO `_regen` (they did not exist before the old path ran);
* acceptance: compared pairs `= 43 (seqTwoMem) + 39 (seqAccSync) = 82`,
  non-zero.

NOT compared: proof terms beyond the constants above. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_memseq_olddata_try Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem "REBUILT"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_memseq_olddata_try Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync "REBUILT"

namespace Tests.Compiler.NoPortsMemSeqGenOldDataTest
open Lean Meta

/-- The lemmas both paths generate for `seqTwoMem` (its audit's list without
`outTy` / `outScalar`). -/
def lemmasTwoMem : List String :=
  ["outsOf", "insOf", "nameOf", "nkOf", "outsNOf", "namesOf", "entry", "calls", "slots",
   "domB", "callWidths", "callArgs", "outChars", "kids", "runFacts",
   "outsG0", "mixedG", "designP0", "alias", "argsN", "fieldOut", "fieldsNd", "outHead",
   "notinP0", "notinP1", "leafNotin0_0", "leafNotin0_1", "leafNotin1_0", "leafNotin1_1",
   "leafNeParent0", "leafNeParent1", "leafNe0_1", "memNe0_1", "iface0", "iface1",
   "kidsP", "sep", "parent", "parentD", "disj", "closes"]

/-- The same for `seqAccSync`. -/
def lemmasAccSync : List String :=
  ["outsOf", "insOf", "nameOf", "nkOf", "outsNOf", "namesOf", "entry", "calls", "slots",
   "domB", "callWidths", "callArgs", "outChars", "kids", "runFacts",
   "outsG0", "mixedG", "designP0", "alias", "argsN", "fieldOut", "fieldsNd", "outHead",
   "notinP0", "leafNotin0_0", "leafNotin1_0",
   "leafNeParent0", "leafNeParent1", "leafNe0_1", "iface0", "iface1",
   "kidsP", "sep", "parent", "parentD", "disj", "closes"]

def lem (f : Name) (s : String) : Name := f ++ Name.mkSimple ("noPortsMemSeq_" ++ s)

def direct (n : Name) : MetaM (Array Name) := do
  match (← getEnv).find? n with
  | some (.thmInfo ti) => return ti.value.getUsedConstants
  | _ => throwError "{n}: not a theorem"

/-- The comparison on one declaration; returns (compared pairs, syntactically
equal types among them). -/
def compare (f : Name) (lemmas : List String) : MetaM (Nat × Nat) := do
  let env ← getEnv
  let shared : List Name := lemmas.map (lem f) ++
    [f ++ `machine_design_noPortsR0, f ++ `machine_design_noPortsR0_closed]
  let mut count := 0
  let mut syn := 0
  for n in shared do
    let r := Tools.ShippingNoPortsKidsCommand.regenName n
    unless env.contains n do throwError "{n}: missing (the generator test is not in the imports)"
    unless env.contains r do throwError "{r}: missing — the previous data path did not rebuild {n}"
    Tests.Compiler.NoPortsTest.stdAxioms r
    let tn := (← getConstInfo n).type
    let tr := (← getConstInfo r).type
    unless ← isDefEq tn tr do
      throwError "{r}: its statement is not that of {n}"
    count := count + 1
    if tn == tr then syn := syn + 1
  -- the four run theorems: the proofs differ as designed
  let outTyN := lem f "outTy"
  let outScN := lem f "outScalar"
  for s in ["runFacts", "outsG0", "mixedG", "designP0"] do
    let n := lem f s
    let r := Tools.ShippingNoPortsKidsCommand.regenName n
    let uNew ← direct n
    let uOld ← direct r
    unless uNew.contains ``Tools.ShippingReaderOutsInv.outTy_of_core && !uNew.contains outTyN do
      throwError "{n}: expected the NEW path's outTy_of_core (and not {outTyN}): {uNew}"
    unless uOld.contains outTyN && !uOld.contains ``Tools.ShippingReaderOutsInv.outTy_of_core do
      throwError "{r}: expected the PREVIOUS path's {outTyN} (and not outTy_of_core): {uOld}"
    if s == "designP0" then
      unless uNew.contains ``Tools.ShippingReaderOutsInv.outScalar_of_core &&
          !uNew.contains outScN do
        throwError "{n}: expected outScalar_of_core (and not {outScN}): {uNew}"
      unless uOld.contains outScN &&
          !uOld.contains ``Tools.ShippingReaderOutsInv.outScalar_of_core do
        throwError "{r}: expected {outScN} (and not outScalar_of_core): {uOld}"
  -- the two decided lemmas: the old path only, generated now
  for n in [outTyN, outScN] do
    unless env.contains n do throwError "{n}: missing — the previous data path decides it"
    Tests.Compiler.NoPortsTest.stdAxioms n
    if env.contains (Tools.ShippingNoPortsKidsCommand.regenName n) then
      throwError "{n}: has a _regen — it existed before the previous path ran (the default path decided it)"
  logInfo m!"NOPORTS MEMSEQ OLDDATA COMPARE {f}: the previous data path rebuilt {count} shared names as …_regen ({syn} of them with syntactically equal types); each rebuilt statement isDefEq the one the default path generated; the run theorems apply outTy_of_core (and designP0 outScalar_of_core) at hcore, entry (new) / {outTyN}, {outScN} (old); {outTyN} and {outScN} were generated by the OLD path only."
  return (count, syn)

end Tests.Compiler.NoPortsMemSeqGenOldDataTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let fs : List (Lean.Name × List String × Nat) :=
    [(``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem,
        Tests.Compiler.NoPortsMemSeqGenOldDataTest.lemmasTwoMem, 43),
     (``Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync,
        Tests.Compiler.NoPortsMemSeqGenOldDataTest.lemmasAccSync, 39)]
  let mut total := 0
  let mut syn := 0
  for (f, ls, expected) in fs do
    let (n, s) ← Tests.Compiler.NoPortsMemSeqGenOldDataTest.compare f ls
    unless n == expected do
      throwError "NOPORTS MEMSEQ OLDDATA COMPARE {f}: {n} pairs compared, expected {expected}"
    total := total + n
    syn := syn + s
  unless total == 82 && total != 0 do
    throwError "NOPORTS MEMSEQ OLDDATA COMPARE: {total} pairs compared, expected 82"
  for n in [``Tools.ShippingReaderOutsInv.outTy_of_core,
      ``Tools.ShippingReaderOutsInv.outScalar_of_core] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  Lean.logInfo m!"NOPORTS MEMSEQ OLDDATA COMPARE: {total} pairs over {fs.length} declarations, all isDefEq ({syn} syntactically equal); per declaration the default path decides 2 output facts fewer (noPortsMemSeq_outTy, noPortsMemSeq_outScalar)."
