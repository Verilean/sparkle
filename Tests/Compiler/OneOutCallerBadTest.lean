import Tests.Compiler.OneOutFamilyTest

/-! # `#machine_oneout` on `callerBad`: one more one-output parent of the gate child `pick` (G1, round par/a-22)

`callerBad` (`Tests/Compiler/ShippingCallsCloseTest.lean` 284–293):

    def callerBad (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let sel ← Signal.reg 0#2
        let acc ← Signal.reg 0#8
        let selS := (sel : Signal defaultDomain (BitVec 2))
        let accS := (acc : Signal defaultDomain (BitVec 8))
        let y := pick selS (accS + x)
        sel <~ selS + (Signal.pure 1#2 : Signal defaultDomain (BitVec 2))
        acc <~ y
        return y

It is the declaration of that file's "a failed generation leaves nothing"
test: `#machine_endpoint callerBad` (304), a deliberately WRONG closing
generation (`failsClean ``callerBad (some 0)`, 367) and then the real
`callerBad.machine_closes_at` (369, by `closesAtTheorem`). No linked,
composed or design-level theorem of it exists; no generator of the
one-output family was run on it.

By READING: a parent WITH two registers and ONE let-bound call of the gate
child `pick`, whose result is the declaration's result — `callerRep`
(`ShippingCallsCloseTest` 57–67) without its second call. The scope of
`#machine_oneout` (`Tools/ShippingOneOutGenCommand.lean`), BUILT on
`caller`, `callerTwice`, `callerD`, `callerNested`, `callerRep`,
`callerInner`, `midH` (`docs/parallel/verification-oneout-family.md`,
`verification-a12.md`, `verification-a13.md`). No new theorem is written in
this file: three BUILT commands are run on one more declaration.

What is NEW against the built one-output parents: nothing by reading of the
shape, except that the call's result is the RETURNED signal itself (`return
y`; in `caller` … `callerRep` the result is a register or the last call's
output — not compared line by line). `callerBad.machine_closes_at` exists
before the first command: `#machine_closes_at` re-derives its statement and
compares (`closesAtTheorem`, `Tools/ShippingMachineClosesAtGen.lean`
228–250), then closes the endpoints generated here.

## EXPECTED (stated before the build; each step THROWS otherwise)

    ONEOUT CALLERBAD DATA …
    callerBad.machine_design_svHR: … (the generator's log line)
    (#machine_closes_at callerBad: its log line; premise EntryDefines pick)
    ONEOUT GEN callerBad: GENERATED [callerBad.machine_design_svH_full, callerBad.machine_design_svH_full_closed] — …
    ONEOUT FULL PREMISE …_closed: run        | binder hr : RunsTo (synthesizeCombinational `callerBad) …
    ONEOUT FULL PREMISE …_closed: reflection | binder entry : MachineDefines … `callerBad callerBad.machineData.shape
    ONEOUT FULL PREMISE …_closed: reflection | binder hR0 : EntryDefines … `pick pick.gateValue
    ONEOUT FULL PREMISE …_closed: ChildBnd   | antecedent under the existentials : ChildBnd mref cref w
    GOALGAP callerBad.machine_design_svH_full_closed_gap … (none NOT ALLOWED)
    ONEOUT FAMILY callerBad: … other: NONE …
    ONEOUT CALLERBAD: …

| endpoint | premise of `callerBad.machine_design_svHR` | predicted state |
|---|---|---|
| `callerBad.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck D.modules b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt callerBad` (open form) | predicted absent in `_closed`, pending build |
| | `hr`, `MachineDefines callerBad`, `EntryDefines pick`, `ChildBnd` | run boundary: they stay premises |

`callerBad.machine_design_svHR` is generated HERE; the audit's inventory
assertion checks that it does ask the four check premises.

## SCOPE (binding for any report)

ONE declaration, `callerBad`: a parent WITH a register, gate child `pick`,
the one-output closing, depth 0. Data conditions decided per declaration
(`callerBad.oneout_*`, `pick.gate_width`, what `#gate_child` left) are
conditions, not reductions; the run, `MachineDefines callerBad`,
`EntryDefines pick`, `ChildBnd` stay premises; compiler guards with
fallback; `DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module
list, not the SV string, not `#sim`. `callerNoEndpoint` (the other
declaration of that failure test) is left WITHOUT an endpoint: its test
asserts that it has none.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``callerBad
  let pk := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick
  let r ← Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [f ++ `machineData, f ++ `machine_ok, f ++ `machine_body, f ++ `machine_sound,
      f ++ `machine_closes_at, f ++ `machine_linked, f ++ `machine_composed,
      f ++ `machine_ships_hierHR, f ++ `machine_design_svHR, f ++ `machine_design_svH_full,
      f ++ `machine_factsH, pk ++ `gate_child, pk ++ `gate_peel, pk ++ `gateValue,
      pk ++ `gate_full, pk ++ `gate_width, ``callerNoEndpoint ++ `machineData] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"ONEOUT CALLERBAD DATA {f}: nDecl={r.nDecl}, binders={r.shape.binders.length}, slots={r.shape.layout.slots.length}, lets={r.shape.layout.lets}, call entries {calls}, argument lets {r.shape.insts.map (·.2.1)}, instFields={r.shape.instFields}, outputs {r.shape.layout.outs.map (·.name)}. In the environment: {have_}; not: {lack}"
  unless calls.eraseDups == [pk] do
    throwError "{f}: the called declarations are {calls.eraseDups}, expected [{pk}]"
  if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
  unless r.shape.instFields.isEmpty do
    throwError "{f}: instFields = {r.shape.instFields} — not the one-output closing"
  for n in [f ++ `machine_sound, f ++ `machine_closes_at, pk ++ `gate_peel] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_design_svHR, f ++ `machine_design_svH_full, f ++ `machine_factsH] do
    if env.contains n then throwError "{n}: exists already (NAME CLASH: another file generates for {f})"

/-! ## The three BUILT commands -/

set_option maxHeartbeats 0 in
#machine_design_svHR callerBad

set_option maxHeartbeats 0 in
#machine_closes_at callerBad

set_option maxHeartbeats 0 in
#machine_oneout_try callerBad "GENERATED"

/-! ## The audit of `OneOutFamilyTest`, on `callerBad`

That audit returns with a SKIPPED log line when no closed endpoint exists;
here that is an ERROR: the constants are asserted first. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``callerBad
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
  -- the other declaration of the failure test keeps no endpoint
  if (← Lean.getEnv).contains (``callerNoEndpoint ++ `machineData) then
    throwError "callerNoEndpoint.machineData: exists — this file must not generate for it"
  let old := f ++ `machine_design_svHR
  Lean.logInfo m!"ONEOUT CALLERBAD: {f} — a parent WITH a register and one let-bound call of the gate child {pk} (the one-output closing). {f}.machine_design_svH_full and its _closed form GENERATED by the built #machine_oneout after {old} (generated in this file, asking A1–A4) and #machine_closes_at (its statement re-derived against the existing {f}.machine_closes_at). SCOPE: one declaration, depth 0, data conditions decided per declaration, compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim; the run, MachineDefines {f}, EntryDefines {pk} and ChildBnd stay premises"
