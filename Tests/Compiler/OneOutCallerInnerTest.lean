import Tests.Compiler.NoPortsMidTest
import Tests.Compiler.OneOutFamilyTest
import Tests.Compiler.ShippingMachineSeqLoopTest

/-! # `#machine_oneout` on `callerInner`: a call inside a flattened sub-machine (G1, round par/a-13)

`callerInner` (`Tests/Compiler/ShippingMachineInstTest.lean`):

    def innerPick (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let c ← Signal.reg 0#8
        let cS := (c : Signal defaultDomain (BitVec 8))
        c <~ Signal.mux en (pick (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)) cS) cS
        return cS

    def callerInner (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
        Signal defaultDomain (BitVec 8) :=
      let s := innerPick en
      circuit do
        let acc ← Signal.reg 0#8
        let accS := (acc : Signal defaultDomain (BitVec 8))
        acc <~ pick (Signal.pure 2#2 : Signal defaultDomain (BitVec 2)) (accS + s + x)
        return accS

By READING: a parent WITH a register, call entries of the ONE gate child
`pick` (one of them inside the flattened sub-machine `innerPick`, whose
register is one of the parent's slots), each call's result ONE
`Signal (BitVec 8)` — so `shape.instFields = []`, the ONE-OUTPUT closing.
Before this round it had `#machine_endpoint` only: no linked / composed /
design-level theorem, hence the REFUSED lines of `OneOutFamilyTest` /
`OneOutAnyFamilyTest` ("no callerInner.machine_ships_hierHR").

What was MEASURED before this file (round par/a-12, the log-only probe
`Tests/Compiler/RemainingProbeTest.lean`, `docs/parallel/verification-a12.md`):

    REMAINING PROBE callerInner: #machine_design_svHR: OK
    REMAINING PROBE callerInner: #machine_closes_at: OK
    REMAINING PROBE callerInner: #machine_oneout: OK
    REMAINING PROBE …callerInner audit: OK — the audit of OneOutFamilyTest ran (… a SKIPPED line there means no closed form)

A probe line counts for nothing (the probe asserts nothing, is not in
`Tests/AllTests.lean`, and its audit line does not say whether the audit
was SKIPPED). THIS file is the proper test: every step THROWS where the
probe would only log, and a SKIPPED audit is an error here.

No new theorem is written in this file: three BUILT commands are run on one
more declaration.

What is NEW against the built one-output parents: the base endpoint
`callerInner.machine_design_svHR` itself (first generated here); a call
whose ARGUMENTS are constants and a sub-machine's register read, inside a
sub-machine's body; two entries of one callee where the entries come from
two different `circuit do` bodies (`callerRep`'s two entries are in one).

## NAME CLASH with the probe (integrator)

`Tests/Compiler/RemainingProbeTest.lean` creates the SAME constants in its
own module (`callerInner.machine_design_svHR`, `callerInner.machine_ships_hierHR`,
`callerInner.machine_closes_at`, `callerInner.oneout_*`,
`callerInner.machine_factsH`, …, `callerInner.machine_design_svH_full(_closed)`,
`…_closed_gap`). This file does NOT import it and it must not import this
file; the two cannot be loaded into one module. Either drop sections (A1)
`mid` and (A3) `callerInner` from the probe, or keep the probe target-built
only (never in `Tests/AllTests.lean`).

The imports: `OneOutFamilyTest` (the audit; it also holds the REFUSED
assertion on `callerInner`, which was true in ITS environment and stays
true there), `ShippingMachineSeqLoopTest`, and `NoPortsMidTest` (which
imports `NoPortsTwoTest`, `ShippingCallsCloseDeepTest`,
`ShippingMachineDepthTest`): together the probe's imports, and `mid`'s
steps before `callerInner`'s as in the probe — the environment before the
first command is the one the probe measured in, minus `loopParent`'s steps.
`NoPortsMidTest` is imported for that reason only; nothing of `mid` is used.
`Tests/Compiler/OneOutAnyFamilyTest.lean` (a sibling in `AllTests`) asserts
REFUSED on `callerInner` in its own environment, which does not contain
this module: unaffected.

## EXPECTED (stated before the build; each command THROWS otherwise)

    callerInner.machine_design_svHR: … (the generator's log line)
    (#machine_closes_at callerInner: its log line; premise EntryDefines pick)
    ONEOUT GEN …callerInner: GENERATED [callerInner.machine_design_svH_full, callerInner.machine_design_svH_full_closed] — …
    ONEOUT FULL PREMISE …_closed: run        | binder hr : RunsTo (synthesizeCombinational `callerInner) …
    ONEOUT FULL PREMISE …_closed: reflection | binder entry : MachineDefines … `callerInner callerInner.machineData.shape
    ONEOUT FULL PREMISE …_closed: reflection | binder hR0 : EntryDefines … `pick pick.gateValue
    ONEOUT FULL PREMISE …_closed: ChildBnd   | antecedent under the existentials : ChildBnd mref cref w
    ONEOUT FULL PREMISE …_closed: reflection | antecedent under the existentials : EntryDefines … `pick pick.gateValue
    GOALGAP callerInner.machine_design_svH_full_closed_gap … (none NOT ALLOWED)
    ONEOUT FAMILY callerInner: … other: NONE …
    ONEOUT CALLERINNER: …

A FAILED outcome is `ONEOUT GEN callerInner: FAILED (data condition … [the
theorem's name]: …)`: then the command throws (the expected class is
GENERATED), nothing is left under the names and NO premise counts as
removed for `callerInner`.

| endpoint | premise of `callerInner.machine_design_svHR` | predicted state |
|---|---|---|
| `callerInner.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck D.modules b` | WRITTEN (this test; the generators are built, the probe logged OK) — predicted absent, pending build |
| | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt callerInner` (open form) | predicted absent in `_closed`, pending build |
| | `hr`, `MachineDefines callerInner`, `EntryDefines pick`, `ChildBnd` | run boundary: they stay premises |

`callerInner.machine_design_svHR` is generated HERE; the audit's inventory
assertion checks that it does ask the four check premises, so that "absent"
is a comparison with a statement of this same build.

## SCOPE (binding for any report)

ONE declaration, `callerInner`: a parent WITH a register, gate child
`pick`, the one-output closing, depth 0. Data conditions decided per
declaration by the kernel (`callerInner.oneout_*`, `pick.gate_width`, what
`#gate_child` left) are conditions, not reductions; the run,
`MachineDefines callerInner`, `EntryDefines pick`, `ChildBnd` stay
premises; the result depends on the compiler's guards with fallback; the
conclusion is about `DesignSV (childMap D.modules) 0 (checkedOptimize b)` —
the module list, not the SV string, not `#sim`. `innerPick` is FLATTENED
into `callerInner` (it is not a module of the design and has no endpoint of
its own here); nothing is claimed about `innerPick` as a declaration.

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner "GENERATED"

/-! ## The audit of `OneOutFamilyTest`, on `callerInner`

That audit returns with a SKIPPED log line when no closed endpoint exists;
here that is an ERROR: the three constants are asserted first. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner
  for n in [f ++ `machine_design_svH_full, f ++ `machine_design_svH_full_closed,
      f ++ `machine_factsH, f ++ `machine_closes_at, f ++ `machine_design_svHR] do
    unless (← Lean.getEnv).contains n do
      throwError "{n}: not generated — the audit would be SKIPPED; no premise counts as removed for {f}"
  Tests.Compiler.OneOutFamilyTest.audit f
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick] false
  -- the audit generated the goal gap; it must exist now
  let gap := f ++ `machine_design_svH_full_closed_gap
  unless (← Lean.getEnv).contains gap do throwError "{gap}: not generated by the audit"
  Tests.Compiler.OneOutFamilyTest.std gap

/-! ## The scope facts this file relies on, asserted on the reader's data -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner
  let pk := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick
  let r ← Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  unless calls.eraseDups == [pk] do
    throwError "{f}: the called declarations are {calls.eraseDups}, expected [{pk}]"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  unless r.shape.instFields.isEmpty do
    throwError "{f}: instFields = {r.shape.instFields} — not the one-output closing"
  unless (← Lean.getEnv).contains (pk ++ `gate_peel) do
    throwError "{pk}: no gate_peel — not a gate child with #gate_child data"
  let full := f ++ `machine_design_svH_full
  let old := f ++ `machine_design_svHR
  Lean.logInfo m!"ONEOUT CALLERINNER: {f} — nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, {calls.length} call entries {calls} (gate child {pk}; by reading the source one entry is inside the flattened sub-machine innerPick — the entry count is the reader's, logged, not asserted), instFields=[], outputs {r.shape.layout.outs.map (·.name)}. Against {old} (generated in this file) the premises shipsHierHCheck, kidsComb, designCheck, outsCheck are absent from {full} and its closed form (the audit above threw otherwise, and a skipped audit is an error here). SCOPE: one declaration, a parent WITH a register, gate children, the one-output closing; data conditions decided per declaration (conditions, not reductions); the run, MachineDefines, EntryDefines and ChildBnd remain premises; compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. innerPick is flattened: nothing is claimed about it as a declaration."
