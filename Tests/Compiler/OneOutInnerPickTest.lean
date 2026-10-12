import Tests.Compiler.OneOutFamilyTest

/-! # `#machine_oneout` on `innerPick` AS AN ENTRY: a gate call that is not let-bound, under a mux (G1, round par/a-22)

`innerPick` (`Tests/Compiler/ShippingMachineInstTest.lean` 99–104):

    def innerPick (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let c ← Signal.reg 0#8
        let cS := (c : Signal defaultDomain (BitVec 8))
        c <~ Signal.mux en (pick (Signal.pure 1#2 : Signal defaultDomain (BitVec 2)) cS) cS
        return cS

It is the sub-machine `callerInner` flattens (`let s := innerPick en`
before `callerInner`'s own `circuit do`). `callerInner`'s endpoint is BUILT
(`Tests/Compiler/OneOutCallerInnerTest.lean`, `docs/parallel/verification-a13.md`)
and says, in its SCOPE, "nothing is claimed about `innerPick` as a
declaration". NO generator was ever run on `innerPick` itself: not
`#machine_endpoint` (it is not a call entry of anything, so no parent's
endpoint generated it), nothing after it.

By READING: as an ENTRY it is a parent WITH a register and ONE call of the
gate child `pick`, the call's result one `Signal (BitVec 8)` — the
one-output closing, the scope of `#machine_oneout`. No new theorem is
written in this file: four BUILT commands are run on one more declaration.

What is NEW against the built one-output parents AS ENTRIES: the call is not
`let`-bound and sits under a `Signal.mux` in a register's next value, with a
constant first argument. `callerInner` contains exactly this call (and one
more of its own), so the reader, the closing and the one-output lemmas have
met it — inside a flattened sub-machine, not as a root.

## EXPECTED (stated before the build; each step THROWS otherwise)

    ONEOUT INNERPICK DATA … (before #machine_endpoint: no innerPick.machineData)
    innerPick.machine_sound: source circuit do → real entry → registers → trace, checked by the kernel
    innerPick.machine_design_svHR: … (the generator's log line)
    (#machine_closes_at innerPick: its log line; premise EntryDefines pick)
    ONEOUT GEN innerPick: GENERATED [innerPick.machine_design_svH_full, innerPick.machine_design_svH_full_closed] — …
    ONEOUT FULL PREMISE …_closed: run        | binder hr : RunsTo (synthesizeCombinational `innerPick) …
    ONEOUT FULL PREMISE …_closed: reflection | binder entry : MachineDefines … `innerPick innerPick.machineData.shape
    ONEOUT FULL PREMISE …_closed: reflection | binder hR0 : EntryDefines … `pick pick.gateValue
    ONEOUT FULL PREMISE …_closed: ChildBnd   | antecedent under the existentials : ChildBnd mref cref w
    GOALGAP innerPick.machine_design_svH_full_closed_gap … (none NOT ALLOWED)
    ONEOUT FAMILY innerPick: … other: NONE …
    ONEOUT INNERPICK: …

| endpoint | premise of `innerPick.machine_design_svHR` | predicted state |
|---|---|---|
| `innerPick.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck D.modules b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt innerPick` (open form) | predicted absent in `_closed`, pending build |
| | `hr`, `MachineDefines innerPick`, `EntryDefines pick`, `ChildBnd` | run boundary: they stay premises |

`innerPick.machine_sound` and `innerPick.machine_design_svHR` are generated
HERE; the audit's inventory assertion checks that the latter does ask the
four check premises.

## What is NOT known before the build

1. whether `#machine_endpoint innerPick` goes through (a root whose only
   call is not `let`-bound; the BUILT instances of such a call are inside
   `callerInner`'s flattened body) — if it does not, the command throws and
   NOTHING below is established;
2. the decided data conditions of `innerPick.oneout_*` (a failure is the
   outcome class FAILED, which the command turns into an error here).

## SCOPE (binding for any report)

ONE declaration, `innerPick`, AS AN ENTRY: a parent WITH a register, gate
child `pick`, the one-output closing, depth 0. Data conditions decided per
declaration; the run, `MachineDefines innerPick`, `EntryDefines pick`,
`ChildBnd` stay premises; compiler guards with fallback; `DesignSV
(childMap D.modules) 0 (checkedOptimize b)` — the module list, not the SV
string, not `#sim`. Nothing is added about `innerPick` inside `callerInner`.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick
  let pk := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick
  let r ← Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [f ++ `machineData, f ++ `machine_ok, f ++ `machine_body, f ++ `machine_sound,
      f ++ `machine_closes_at, f ++ `machine_ships_hierHR, f ++ `machine_design_svHR,
      f ++ `machine_design_svH_full, f ++ `machine_factsH, pk ++ `gate_child, pk ++ `gate_peel,
      pk ++ `gateValue, pk ++ `gate_full, pk ++ `gate_width] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"ONEOUT INNERPICK DATA {f}: nDecl={r.nDecl}, binders={r.shape.binders.length}, slots={r.shape.layout.slots.length}, lets={r.shape.layout.lets}, call entries {calls}, argument lets {r.shape.insts.map (·.2.1)}, instFields={r.shape.instFields}, outputs {r.shape.layout.outs.map (·.name)}. In the environment: {have_}; not: {lack}"
  unless calls.eraseDups == [pk] do
    throwError "{f}: the called declarations are {calls.eraseDups}, expected [{pk}]"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  unless r.shape.instFields.isEmpty do
    throwError "{f}: instFields = {r.shape.instFields} — not the one-output closing"
  unless env.contains (pk ++ `gate_peel) do
    throwError "{pk}: no gate_peel — not a gate child with #gate_child data"
  for n in [f ++ `machineData, f ++ `machine_sound, f ++ `machine_design_svHR,
      f ++ `machine_design_svH_full, f ++ `machine_closes_at] do
    if env.contains n then
      throwError "{n}: exists already — this file is written for a declaration no generator was run on (NAME CLASH)"

/-! ## The four BUILT commands -/

set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick

set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick "GENERATED"

/-! ## The audit of `OneOutFamilyTest`, on `innerPick`

That audit returns with a SKIPPED log line when no closed endpoint exists;
here that is an ERROR: the constants are asserted first. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick
  let pk := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick
  for n in [f ++ `machine_design_svH_full, f ++ `machine_design_svH_full_closed,
      f ++ `machine_factsH, f ++ `machine_closes_at, f ++ `machine_design_svHR] do
    unless (← Lean.getEnv).contains n do
      throwError "{n}: not generated — the audit would be SKIPPED; no premise counts as removed for {f}"
  Tests.Compiler.OneOutFamilyTest.audit f [pk] false
  -- the audit generated the goal gap; it must exist now
  let gap := f ++ `machine_design_svH_full_closed_gap
  unless (← Lean.getEnv).contains gap do throwError "{gap}: not generated by the audit"
  Tests.Compiler.OneOutFamilyTest.std gap
  let old := f ++ `machine_design_svHR
  Lean.logInfo m!"ONEOUT INNERPICK: {f} AS AN ENTRY — a parent WITH a register and one call of the gate child {pk} that is not let-bound (under a mux, constant first argument); the one-output closing. {f}.machine_design_svH_full and its _closed form GENERATED by the built #machine_oneout after #machine_endpoint, {old} (asking A1–A4) and #machine_closes_at, all run in this file. SCOPE: one declaration, depth 0, data conditions decided per declaration, compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim; the run, MachineDefines {f}, EntryDefines {pk} and ChildBnd stay premises. Nothing is added about {f} inside callerInner"
