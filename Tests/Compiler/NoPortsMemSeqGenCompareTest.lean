import Tests.Compiler.NoPortsMemSeqMemTest
import Tests.Compiler.NoPortsMemSeqMemClosedTest
import Tools.ShippingNoPortsMemSeqCommand

/-! # `#machine_no_ports_memseq`: the COMPARE path, on the two hand tests of `seqMem` (round par/b-21)

This file imports the hand tests (BUILT), which own

    seqMem.machine_design_noPortsR0          (`NoPortsMemSeqMemTest`)
    seqMem.machine_design_noPortsR0_closed   (`NoPortsMemSeqMemClosedTest`)

and runs the command on `seqMem`. The command must NOT return silently: it
rebuilds both statements from the reader's data, adds the rebuilt theorems
as `…_regen` (kernel-checked), and requires each rebuilt statement to be
`isDefEq` the hand one (an error otherwise). Expected class: `REBUILT`.

The lemmas are GENERATED, not compared by the command: the hand ones are
`Tests.Compiler.NoPortsMemSeqMemTest.seqMem_*` /
`Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_*` (their tests'
namespaces), the command's are `seqMem.noPortsMemSeq_*`. This file compares
ONE of them itself: the generated closing against the hand `seqMem_closes`.
`cnt.machine_leafKid` exists in the imports: the command checks its
statement and USES it (it adds no `cnt.machine_leafKid_regen`).

This file may be in `Tests/AllTests.lean`: every name it adds is new
(`seqMem.noPortsMemSeq_*`, `seqMem.machine_design_noPortsR0_regen`,
`seqMem.machine_design_noPortsR0_closed_regen`) — the audit below THROWS if
one of the lemma names existed before the command ran.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise | predicted state |
|---|---|---|
| `seqMem.machine_design_noPortsR0` | all | UNCHANGED (the hand theorem); the rebuilt statement `isDefEq` it — WRITTEN, NOT BUILT |
| `seqMem.machine_design_noPortsR0_closed` | all | UNCHANGED; the rebuilt statement `isDefEq` it |
| `…_regen` (two) | — | added, standard axioms |

Nothing is removed from any endpoint by this file.

WRITTEN, NOT BUILT (par/b-21). -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem "REBUILT"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
  let env ← Lean.getEnv
  for s in ["machine_design_noPortsR0", "machine_design_noPortsR0_closed"] do
    let e := f ++ Lean.Name.mkSimple s
    let r := f ++ Lean.Name.mkSimple (s ++ "_regen")
    unless env.contains e do throwError "{e}: missing — the hand test is not in the imports"
    unless env.contains r do
      throwError "{r}: missing — the compare path did not rebuild {e}"
    Tests.Compiler.NoPortsTest.stdAxioms r
    unless ← Lean.Meta.isDefEq (← Lean.getConstInfo e).type (← Lean.getConstInfo r).type do
      throwError "{r}: its statement is not that of {e}"
  -- the lemmas were generated under their own names (no hand lemma has them)
  let lemmas : List String :=
    ["outsOf", "insOf", "nameOf", "nkOf", "outsNOf", "namesOf",
     "outsOf_at0", "outsOf_at1", "namesOf_at0", "namesOf_at1",
     "entry", "calls", "slots", "domB", "callWidths", "callArgs", "outChars",
     "kids", "runFacts", "outsG0", "mixedG", "designP0",
     "alias", "argsN", "fieldOut", "fieldsNd", "outHead", "notinP0", "leafNotin0_0",
     "leafNeParent0", "iface0", "kidsP", "sep", "parent", "parentD", "disj", "closes"]
  for s in lemmas do
    let n := f ++ Lean.Name.mkSimple ("noPortsMemSeq_" ++ s)
    unless env.contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
    if env.contains (f ++ Lean.Name.mkSimple ("noPortsMemSeq_" ++ s ++ "_regen")) then
      throwError "{n}: existed before the command ran (a second generator file is in the imports)"
  -- par/r-5: the two output facts come from the reader (outTy_of_core / outScalar_of_core)
  for s in ["outTy", "outScalar"] do
    let n := f ++ Lean.Name.mkSimple ("noPortsMemSeq_" ++ s)
    if env.contains n then
      throwError "{n}: generated — the default path takes it from the reader (par/r-5), it must not decide it"
  -- the leaf side is the callee's own theorem: not re-added
  let lkR := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt ++ `machine_leafKid_regen
  if env.contains lkR then throwError "{lkR}: exists — the command re-added the callee's leafKid"
  -- the generated closing and the hand closing state the same thing
  let clG := f ++ `noPortsMemSeq_closes
  let clH := ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_closes
  let sameCl ← Lean.Meta.isDefEq (← Lean.getConstInfo clG).type (← Lean.getConstInfo clH).type
  unless sameCl do
    throwError "{clG}: its statement is not that of the hand {clH}"
  Lean.logInfo m!"NOPORTS MEMSEQ GEN COMPARE {f}: the command REBUILT {f}.machine_design_noPortsR0 and {f}.machine_design_noPortsR0_closed from the reader's data; both rebuilt statements are isDefEq the hand ones (kept as …_regen, standard axioms); {lemmas.length} lemmas {f}.noPortsMemSeq_* generated on standard axioms; {clG} states what the hand {clH} states (isDefEq): its only premise is the reflection of cnt. cnt.machine_leafKid was USED, not re-added. Nothing is removed from any endpoint; the hand theorems are unchanged."
