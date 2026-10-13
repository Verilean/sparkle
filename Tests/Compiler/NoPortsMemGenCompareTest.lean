import Tests.Compiler.NoPortsMemOnlyClosedMemCounterTest
import Tools.ShippingNoPortsMemCommand

/-! # `#machine_no_ports_mem`: the COMPARE path, on one hand test (`memCounter`) (round par/b-20)

This file imports the hand test `NoPortsMemOnlyClosedMemCounterTest` (BUILT),
which owns

    memCounter.machine_design_noPortsR0          (`NoPortsMemOnlyAtMemCounterTest`)
    memCounter.machine_design_noPortsR0_closed   (`NoPortsMemOnlyClosedMemCounterTest`)

and runs the command on `memCounter`. The command must NOT return silently:
it rebuilds both statements from the reader's data, adds the rebuilt
theorems as `…_regen` (kernel-checked), and requires each rebuilt statement
to be `isDefEq` the hand one (an error otherwise). Expected class: `REBUILT`.

The lemmas are GENERATED, not compared: the hand ones are
`Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_data`, … (their test's
namespace), the command's are `memCounter.noPortsMem_*`.

NEVER co-import with `Tests.Compiler.NoPortsMemGenFamilyTest` (it creates
`memCounter.machine_design_noPortsR0` itself). This file may be in
`Tests/AllTests.lean`: every name it adds is new (`memCounter.noPortsMem_*`,
`memCounter.machine_design_noPortsR0_regen`, `…_closed_regen`).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise | predicted state |
|---|---|---|
| `memCounter.machine_design_noPortsR0` | all | UNCHANGED (the hand theorem); the rebuilt statement `isDefEq` it — WRITTEN, NOT BUILT |
| `memCounter.machine_design_noPortsR0_closed` | all | UNCHANGED; the rebuilt statement `isDefEq` it |
| `…_regen` (two) | — | added, standard axioms |

Nothing is removed from any endpoint by this file.

WRITTEN, NOT BUILT (par/b-20). -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_mem_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "REBUILT"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter
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
  -- (par/b-30: `notin0` is no longer generated — the closing has no name lemma)
  for s in ["entry", "data", "runFacts", "outsG0", "kidsMemG", "designP0", "closeData",
      "closes"] do
    let n := f ++ Lean.Name.mkSimple ("noPortsMem_" ++ s)
    unless env.contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
    if env.contains (f ++ Lean.Name.mkSimple ("noPortsMem_" ++ s ++ "_regen")) then
      throwError "{n}: existed before the command ran (a second generator file is in the imports)"
  -- the generated closing and the hand closing state the same thing
  let clG := f ++ `noPortsMem_closes
  let clH := ``Tests.Compiler.NoPortsMemOnlyClosedMemCounterTest.memCounter_closes
  let sameCl ← Lean.Meta.isDefEq (← Lean.getConstInfo clG).type (← Lean.getConstInfo clH).type
  unless sameCl do
    throwError "{clG}: its statement is not that of the hand {clH}"
  let dG := f ++ `noPortsMem_data
  let dH := ``Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_data
  let sameD ← Lean.Meta.isDefEq (← Lean.getConstInfo dG).type (← Lean.getConstInfo dH).type
  unless sameD do
    throwError "{dG}: its statement is not that of the hand {dH}"
  Lean.logInfo m!"NOPORTS MEM GEN COMPARE {f}: the command REBUILT {f}.machine_design_noPortsR0 and {f}.machine_design_noPortsR0_closed from the reader's data; both rebuilt statements are isDefEq the hand ones (kept as …_regen, standard axioms); {clG} and {dG} state what the hand {clH} and {dH} state (isDefEq). Nothing is removed from any endpoint; the hand theorems are unchanged."
