import Lean.Elab.Command
import Tests.Compiler.OneOutWKeccakFTest
import Tests.Compiler.NoPortsGrandHBTest
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingChildIfaceGen
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingBoundaryClose
import Tools.ShippingFinalGoalCommand
import Tests.Compiler.KeccakSpongeLogLib

/-! # `#machine_no_ports_kids` on `keccak256SpongeHW` AS AN ENTRY: the sponge over `wKeccakF` (G1, round par/a-29)

WRITTEN, NOT BUILT, NOT RUN. Modelled on `Tests/Compiler/NoPortsKidsMid2Test.lean`
(BUILT, in `Tests/AllTests.lean`): no new theorem is written in this file,
BUILT commands are run on one more declaration and the audit of `mid2` is
applied to what they leave. Every step ASSERTS (an error stops the file),
except step 5 (log-only, see below). Details and the reading behind every
prediction: `docs/parallel/A-keccak-sponge.md`.

`keccak256SpongeHW` (`IP/Crypto/Keccak256Sponge.lean` 94–257) by the reader
(MEASURED, `docs/parallel/A-keccak.md` 29–35): `nDecl = 37`, 129 binders, 30
registers, 27 call entries of ONE callee `wKeccakF` in ONE (callee, argument
lets) group of 26 lets, `instFields` = `l0 … l24, round, done` (27) — the
GENERAL closing —, 5 outputs. `wKeccakF`: a register machine (27 slots) with
ONE one-output call of the gate child `keccakRcHW`. That is `mid2 → midH →
rcH`'s class; new against `mid2`: 27 entries of one instance, a 27-output /
26-argument child, 1606 + 1607 state bits.

## For the integrator: HEAVY — TARGET-ONLY, never imported, not for `Tests/AllTests.lean`

    SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/noports-keccak-sponge.log \
      ~/sparkle-work/bin/cgrun.sh -n noports-sponge -m 3G -s 0 -t 3600 -- \
      lake build Tests.Compiler.NoPortsKeccakSpongeTest

(a fresh progress file each run; without the variable the generators write
no progress line and this file's lines go to `.lake/noports-keccak-sponge.log`).
MEASURED before (the grouped probe, removed in round par/b-28;
`docs/parallel/A-depth-grouped.md` "Run record 2"): step 3 alone 489 s; the base of `wKeccakF` ≈ 2 min — here it is
IMPORTED (`OneOutWKeccakFTest`, BUILT target-only; if its `.olean` is absent
or stale lake builds it first, ≈ 3 min more). Steps 4–10 were never run.

NAME CLASH: this file ADDS `keccak256SpongeHW.machine_sound`,
`.machine_composedNR1`, `.machine_ships_hierNR1`, `.machine_design_svNR1`,
`.closes_deep`, `.machine_design_noPortsNR1*`, `wKeccakF.closes_deep`,
`wKeccakF.iface_deep`, `wKeccakF.machine_oneOutKid`, …; it takes
`keccakRcHW.gate_*` and `wKeccakF.machine_*` / `.oneout_*` from
`OneOutWKeccakFTest`. NEVER import it together with `KeccakProbeTest`,
`KeccakSpongeStepProbe`, `KeccakSpongeStepProbe2`, `DepthSwitchSpongeTest`
(they generate the same constants; step 1 throws when one is there).

ROUND par/b-28 (WRITTEN, NOT BUILT in this form): step 3 runs the switched
`#machine_design_svNR keccak256SpongeHW 1` DIRECTLY (its loop is the grouped
one, `Tools/ShippingMachineDepthCommandR.lean`). Until then it ran the
separate grouped command `#machine_design_svNRG … 1 as_old`
(`Tools/ShippingMachineDepthCommandRG.lean`, removed: a duplicate of that
loop), and that is the form in which this file was BUILT (run
`20261013-150059-switch-sponge`). The switched command on the sponge in the
closure of `OneOutWKeccakFTest` was BUILT separately
(`Tests/Compiler/DepthSwitchSpongeTest.lean`, run
`20261013-151138-switch-sponge-direct`); this file's closure has more imports,
so step 3 here is that run's command, not that run. Steps 4–10 read
`machine_ships_hierNR1` / `machine_design_svNR1` by name: both commands build
them by the same `generateDesignNR` over a composed theorem with the same
statement (`docs/parallel/depth-switch-evidence.md`).

## The recursion-depth failure of the probe's step 9 (diagnosis)

READ: `#machine_closes_deep` runs its generator under
`withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })`
(`Tools/ShippingChildIfaceGen.lean` 389–390): the AMBIENT options with
`async` off, no `maxRecDepth` of its own. Its generated `theorem` commands
(`elabCommand`, lines 124, 245, 356) carry no `set_option`. In this
toolchain (v4.32.1) a theorem's body is elaborated under `withOptions`
(`Lean/Elab/MutualDef.lean` 1387) and `CoreM`'s `withOptions` sets
`maxRecDepth := maxRecDepth.get options` (`Lean/CoreM.lean` 288): the limit
of the generated proof IS the scope's option — the default 512 in the probe
(its step 9 had only `maxHeartbeats 0`), as in every BUILT use
(`ShippingCallsCloseDeepTest` 26–33: no `maxRecDepth`, small declarations).
So the test sets it: `set_option maxRecDepth 1000000 in` before the command
(the command form also sets the command state's cached limit,
`Lean/Elab/BuiltinCommand.lean` 519). No change under `Tools/` is needed.

INFERRED (the probe's message is cut after the first line): the failing
tactic is one of the 14 `by decide` of `wKeccakF.iface_deep`
(`ShippingChildIfaceGen.lean` 366–368, the data hypotheses of
`kidsChild_of_real`, `Tools/ShippingKidsChildIface.lean` 357–374) over
`wKeccakF.machineData` — 124 binders: `hdomB` ranges over 97 binders, `hSL`
over 96, `hC` is `callsOk 27`. The SAME facts are decided for `wKeccakF` by
`#machine_oneout` (`oneout_callsOk`, `oneout_domB`, …) under
`maxRecDepth 100000`, which that generator sets itself
(`Tools/ShippingOneOutGenCommand.lean` 217) — and they passed there
(MEASURED: step 11 of the probe, OK in 19.6 s). NOT known: which of the 14.

## The steps (each: `NKS STEP START …` before, `OK (ms)` / `FAILED (ms) — …` after, in the progress file)

| step | what | a failure means |
|---|---|---|
| 0 | which progress variable is set | — |
| 1 | reader data of the sponge and `wKeccakF`, LOGGED; class and imports asserted | the READING of the header is wrong, or a name clash / a missing base constant |
| 2 | `#machine_endpoint keccak256SpongeHW` | the base differs from the probe's (its step 6 was OK) |
| 3 | `#machine_design_svNR keccak256SpongeHW 1` (the switched command; before round par/b-28: `#machine_design_svNRG … 1 as_old`) | not reproducible (489 s OK in the grouped probe, there with `wKeccakF`'s `svHR` / `oneout` generated AFTER it; here they are imported BEFORE; the switched command alone: BUILT in `DepthSwitchSpongeTest`) |
| 4 | `#machine_closes_deep keccak256SpongeHW`, `maxRecDepth 1000000` | the option is not the whole story: the message names the theorem (`wKeccakF.iface_deep`, or the sponge's own `closes_deep`: 27 nested `cases`, decides over 27 entries); or a real refusal |
| 5a–c | LOG-ONLY: the command's own generator functions, one per line — `wKeccakF.machine_oneOutKid`; `…machine_kidsK1`; the four run theorems | nothing (the environment is put back; step 6 generates what is missing) — the lines say WHICH lemma is slow or fails |
| 6 | `#machine_no_ports_kids keccak256SpongeHW 1`, `maxRecDepth 1000000` | a decided data condition fails (the message names the theorem), or the head / closed form does not assemble (binder order) |
| 7 | `#machine_boundary_close …noPortsNR1_closed` | a conjunct of the run boundary is not derived from the binders (it is KEPT and printed by step 9 — then `_closedB` has more than `ChildBnd`) |
| 8 | `#machine_goal_gap_of …_closedB` | the reporter does not read the statement |
| 9 | premise listing of the open, closed and `B` forms and their antecedents (logged, nothing asserted but existence) | — |
| 10 | the audit of `mid2`, on the sponge | see the table below: the first violated line is the error |

## EXPECTED — endpoint, premise, predicted state (all WRITTEN, NOT BUILT)

| endpoint | premise | predicted state |
|---|---|---|
| `keccak256SpongeHW.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` of `…machine_design_svNR1` | predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt keccak256SpongeHW` (open form) | predicted absent in `_closed` (`keccak256SpongeHW.closes_deep`), pending build |
| `…noPortsNR1_closedB` (+ `_gap`) | the boundary's `MachineDefines wKeccakF`, `True`, ∀-contexts conjunct (NOT ALLOWED) | predicted absent from the antecedent (only `ChildBnd` stays), as `mid2` / `grandH` (BUILT); 0 NOT ALLOWED; no gap hypothesis |
| | `hr`, `MachineDefines keccak256SpongeHW`, `MachineDefines wKeccakF`, `EntryDefines keccakRcHW`, `ChildBnd` | run boundary: they stay premises |

The closed form's proposition binders: 4 ASSERTED (the run and one
reflection each of the sponge, `wKeccakF`, `keccakRcHW`), LOGGED before the
assertion. A name-separation premise (`hN_…`) would be a fifth binder and an
error: predicted none (the three names differ in their last component; the
outputs `d0 … d3`, `done` do not start with `i`), by reading only.

## SCOPE (binding for any report)

ONE declaration, `keccak256SpongeHW`, AS AN ENTRY: a domain-polymorphic
parent WITH registers under the general closing, one callee (`wKeccakF`: a
register machine with a one-output call of the gate child `keccakRcHW`),
depth 1. Data conditions decided per declaration by the kernel are
conditions, not reductions; compiler guards with fallback; `DesignSV` of the
module list — not the SV string, not `#sim`; the run, the three reflections
and `ChildBnd` stay premises. NOT covered and NOT implied: Keccak's FUNCTION
(this is the compiler's correctness on one declaration, not that the
declaration computes Keccak-256); `keccakF1600HW` under its own name; the
sponge as a child of anything.

UNVERIFIED at the time of writing: this file was not built. -/

namespace Tests.Compiler.NoPortsKeccakSpongeTest
open Lean Meta Elab Command

/-- The file the lines go to without the progress variable. -/
def fallback : String := ".lake/noports-keccak-sponge.log"

/-- A line: to the progress file now, to the message log when the command ends. -/
def note (msg : String) : CommandElabM Unit := do
  Tests.Compiler.KeccakSpongeLogLib.toFile fallback msg
  logInfo m!"{msg}"

/-- One step (the wrapper of the former `KeccakSpongeGroupedProbe`, BUILT, with an
asserting mode). `START` is written BEFORE the action; then `OK (ms)` with
the action's information messages, or `FAILED (ms) — message`. With
`must = true` a failure is an ERROR after its line (the messages stay);
with `must = false` the environment and the message log are put back and
the file goes on. -/
def runStep (label : String) (must : Bool) (act : CommandElabM Unit) : CommandElabM Unit := do
  note s!"NKS STEP START {label}"
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let t0 ← IO.monoMsNow
  let res : Option String ← try
      act
      pure none
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (some msg)
  let t1 ← IO.monoMsNow
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match res with
    | some msg => some msg
    | none => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  match failure with
  | some msg =>
    if must then
      note s!"NKS STEP {label}: FAILED ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}"
      throwError "NKS STEP {label}: FAILED — {msg}"
    else
      setEnv savedEnv
      modify fun s => { s with messages := savedMsgs }
      note s!"NKS STEP {label}: FAILED ({t1 - t0} ms), LOG ONLY, the environment put back — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}"
  | none =>
    let infos ← (msgs.filter (·.severity == .information)).mapM fun m => m.data.toString
    for i in infos do
      Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"  | {Tests.Compiler.KeccakSpongeLogLib.clipStr i 3000}"
    note s!"NKS STEP {label}: OK ({t1 - t0} ms)"

/-- `#nks_step "label" in cmd`: a command as an ASSERTING step. -/
elab "#nks_step " tag:str " in " c:command : command => do
  runStep tag.getString true (elabCommand c)

/-- `#nks_env "label"`: is the generators' progress variable set? -/
elab "#nks_env " tag:str : command => do
  let isSet ← Tests.Compiler.KeccakSpongeLogLib.progressSet
  note s!"NKS STEP {tag.getString} SPARKLE_MACHINE_PROGRESS set: {isSet} (when false the generators write NO progress line and this file's lines are in {fallback})"

/-- `#nks_pieces f n`: LOG-ONLY. The generator functions `#machine_no_ports_kids
f n` itself calls (`Tools.ShippingNoPortsKidsCommand.noPortsKids` 644–658:
`scopeK`, `oneOutKidTheorem`, `kidsTheorem`, `runTheorems`), each as a step
of its own, so that the progress file says which generated lemma is slow or
fails. The command proper (the next step) finds what was generated here in
the environment and reuses it — each of these functions returns the existing
constant — and generates what a failed piece left out. Leaf callees are not
handled here (the sponge has none); nothing here asserts. -/
elab "#nks_pieces " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let depth : Nat := n.getNat
  let scope? : Option (Tools.ShippingMachineCommand.Read × List Name ×
      List (Name × Tools.ShippingNoPortsKidsCommand.Kind)) ← try
      let x ← Tools.ShippingNoPortsKidsCommand.scopeK f depth
      pure (some x)
    catch ex =>
      let msg ← ex.toMessageData.toString
      note s!"NKS STEP 5 pieces of {f}: the scope REFUSES (log only) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}"
      pure none
  let some (r, calls, kinds) := scope? | return
  let mut gates : List Name := []
  for (_, kd) in kinds do
    match kd with
    | Tools.ShippingNoPortsKidsCommand.Kind.oneOut g _ =>
      unless gates.contains g do gates := gates ++ [g]
    | Tools.ShippingNoPortsKidsCommand.Kind.leaf => pure ()
  for (k, kd) in kinds do
    match kd with
    | Tools.ShippingNoPortsKidsCommand.Kind.oneOut g nD =>
      runStep s!"5a {k}.machine_oneOutKid (once per callee; gate child {g}, nDecl {nD})" false
        (discard <| withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
          (Tools.ShippingNoPortsKidsCommand.oneOutKidTheorem k g nD))
    | Tools.ShippingNoPortsKidsCommand.Kind.leaf =>
      note s!"NKS STEP 5a {k}: a leaf callee — not generated here (the command does it)"
  let ctxK : Tools.ShippingNoPortsKidsCommand.Ctx :=
    { f := f, n := depth, nDecl := r.nDecl, calls := calls, kinds := kinds, gates := gates }
  let kidsName : Name := f ++ Name.mkSimple s!"machine_kidsK{depth}"
  runStep s!"5b {kidsName} (KidFacts of the {calls.length} call entries)" false
    (discard <| withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
      (Tools.ShippingNoPortsKidsCommand.kidsTheorem ctxK))
  let envNow ← getEnv
  if envNow.contains kidsName then
    runStep s!"5c the four run theorems of {f} (machine_runFactsK{depth}, machine_outsGK{depth}, machine_maskedGK{depth}, machine_designPK{depth}: callWidthsOk decided twice, callArgsOk once)" false
      (discard <| withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
        (Tools.ShippingNoPortsKidsCommand.runTheorems ctxK kidsName))
  else
    note s!"NKS STEP 5c: SKIPPED — {kidsName} is not in the environment"

end Tests.Compiler.NoPortsKeccakSpongeTest

/-! ## Step 0: the progress variable -/

#nks_env "0"

/-! ## Step 1: the reader's data, LOGGED first, then the class and the imports asserted -/

set_option maxHeartbeats 0 in
#nks_step "1 reader data, class, imports" in
  run_cmd Lean.Elab.Command.liftTermElabM do
    let f := ``Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW
    let m := ``Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF
    let rc := ``Sparkle.IP.Crypto.Keccak256HW.keccakRcHW
    let env ← Lean.getEnv
    for n in [f, m, rc] do
      unless env.contains n do throwError "{n}: not in the environment (a wrong NAME in this file)"
    let r ← Tools.ShippingMachineCommand.readMachine f
    Lean.logInfo m!"NOPORTS SPONGE DATA {f}: {Tests.Compiler.KeccakSpongeLogLib.describeRead r}"
    let mr ← Tools.ShippingMachineCommand.readMachine m
    Lean.logInfo m!"NOPORTS SPONGE DATA callee {m}: {Tests.Compiler.KeccakSpongeLogLib.describeRead mr}"
    let needed : List Lean.Name :=
      [m ++ `machineData, m ++ `machine_ok, m ++ `machine_body, m ++ `machine_sound,
       m ++ `machine_closes_at, m ++ `machine_portsRawH, m ++ `oneout_callsOk,
       m ++ `oneout_slotLen, m ++ `oneout_domB, m ++ `oneout_insts, m ++ `oneout_instFields,
       -- `oneout_outTy` / `oneout_outScalar` are no longer generated (#machine_oneout takes them from
       -- the reader, par/r-5); `oneOutKidTheorem` decides them for the callee
       m ++ `oneout_slots, m ++ `oneout_outChars,
       m ++ `oneout_nomem, rc ++ `gate_peel, rc ++ `gate_old, rc ++ `gate_wf,
       rc ++ `gateBinders, rc ++ `gateSort, rc ++ `gate_full, rc ++ `gate_kidK,
       rc ++ `gateValue, rc ++ `gate_child]
    let fresh : List Lean.Name :=
      [f ++ `machineData, f ++ `machine_sound, f ++ `machine_composedNR1,
       f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1,
       f ++ `closes_deep, f ++ `machine_kidsK1, f ++ `machine_runFactsK1,
       f ++ `machine_design_noPortsNR1, f ++ `machine_design_noPortsNR1_closed,
       m ++ `closes_deep, m ++ `iface_deep, m ++ `machine_oneOutKid]
    let mut have_ : List Lean.Name := []
    let mut lack : List Lean.Name := []
    for n in needed ++ fresh do
      if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
    Lean.logInfo m!"NOPORTS SPONGE DATA: in the environment before the commands: {have_}; not: {lack}"
    -- the class the header states
    unless (r.shape.insts.map (·.1)).eraseDups == [m] do
      throwError "{f}: the called declarations are {(r.shape.insts.map (·.1)).eraseDups}, expected [{m}]"
    if r.shape.layout.slots.isEmpty then throwError "{f}: no register"
    if r.shape.instFields.isEmpty then throwError "{f}: instFields = [] — not the general closing"
    unless (mr.shape.insts.map (·.1)).eraseDups == [rc] do
      throwError "{m}: the called declarations are {(mr.shape.insts.map (·.1)).eraseDups}, expected [{rc}]"
    unless mr.shape.instFields.isEmpty do
      throwError "{m}: instFields = {mr.shape.instFields} — not the one-output closing"
    if mr.shape.layout.slots.isEmpty then throwError "{m}: no register"
    -- what this file builds on, and what it must be the first to add
    for n in needed do
      unless env.contains n do
        throwError "{n}: not in the imports (this file builds on it: OneOutWKeccakFTest)"
    for n in fresh do
      if env.contains n then
        throwError "{n}: exists already — a Keccak probe is imported (NAME CLASH, see the header)"

/-! ## Steps 2–3: the base of the sponge (the probe's steps 6 and 8) -/

set_option maxHeartbeats 0 in
#nks_step "2 keccak256SpongeHW #machine_endpoint" in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

set_option maxHeartbeats 0 in
#nks_step "3 keccak256SpongeHW #machine_design_svNR 1 (the switched command)" in
  #machine_design_svNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1

/-! ## Step 4: the closing over the child with calls — under the recursion-depth option (see the header) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#nks_step "4 keccak256SpongeHW #machine_closes_deep (maxRecDepth 1000000)" in
  #machine_closes_deep Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

/-! ## Step 5 (LOG-ONLY): the generated lemmas of step 6, one line each -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#nks_pieces Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1

/-! ## Steps 6–8: the BUILT commands, as `NoPortsKidsMid2Test` -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#nks_step "6 keccak256SpongeHW #machine_no_ports_kids 1" in
  #machine_no_ports_kids Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1

set_option maxHeartbeats 0 in
#nks_step "7 keccak256SpongeHW #machine_boundary_close" in
  #machine_boundary_close
    Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#nks_step "8 keccak256SpongeHW #machine_goal_gap_of" in
  #machine_goal_gap_of
    Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closedB

/-! ## Step 9: the premise listing (logged BEFORE the audit asserts anything)

Per theorem: every binder with its class, and the antecedents under the
existentials — the conjuncts `#machine_boundary_close` KEPT are the
antecedents of `…_closedB` printed here. -/

set_option maxHeartbeats 0 in
#nks_step "9 premise listing" in
  run_cmd Lean.Elab.Command.liftTermElabM do
    let f := ``Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW
    for n in [f ++ `machine_design_noPortsNR1, f ++ `machine_design_noPortsNR1_closed,
        f ++ `machine_design_noPortsNR1_closedB] do
      let ci ← Lean.getConstInfo n
      let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines n
      let inner ← Lean.Meta.forallTelescope ci.type fun _ body =>
        Tests.Compiler.NoPortsTest.innerAntecedents body
      let innerLines : List String := inner.toList.map fun a =>
        (if a.2 then "ALLOWED     " else "NOT ALLOWED ") ++ a.1
      Lean.logInfo m!"NOPORTS SPONGE LISTING {n}: {lines.size} binder / premise lines, {bad.size} NOT ALLOWED among the binders; {inner.size} antecedent(s) under the existentials.\n{String.intercalate "\n" lines.toList}\nANTECEDENTS UNDER THE EXISTENTIALS:\n{String.intercalate "\n" innerLines}"

/-! ## Step 10: the audit (an error on any failure) — the audit of `NoPortsKidsMid2Test`, on the sponge -/

set_option maxHeartbeats 0 in
#nks_step "10 audit" in
  run_cmd Lean.Elab.Command.liftTermElabM do
    let f := ``Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW
    let m := ``Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF
    let rc := ``Sparkle.IP.Crypto.Keccak256HW.keccakRcHW
    -- (1) the generated lemmas, on standard axioms
    for n in [m ++ `machine_oneOutKid, f ++ `machine_kidsK1, f ++ `machine_runFactsK1,
        f ++ `machine_outsGK1, f ++ `machine_maskedGK1, f ++ `machine_designPK1, f ++ `closes_deep,
        m ++ `closes_deep, m ++ `iface_deep] do
      unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
      Tests.Compiler.NoPortsTest.stdAxioms n
    -- (2) GENERATED (no `_regen`), no checker constant; the base asks the four
    let old := f ++ `machine_design_svNR1
    let openN := f ++ `machine_design_noPortsNR1
    let closed := f ++ `machine_design_noPortsNR1_closed
    for n in [openN, closed] do
      unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
      Tests.Compiler.NoPortsTest.stdAxioms n
      let ci ← Lean.getConstInfo n
      for k in Tests.Compiler.NoPortsTest.checkers do
        if (ci.type.find? (·.isConstOf k)).isSome then throwError "{n}: the statement mentions {k}"
    if (← Lean.getEnv).contains (f ++ `machine_design_noPortsNR1_regen) then
      throwError "{openN}: existed before this file (the compare path ran: NAME CLASH)"
    let oldT := (← Lean.getConstInfo old).type
    for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
        ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
        ``Tools.ShippingDesignSVBack.outsCheck] do
      unless (oldT.find? (·.isConstOf k)).isSome do
        throwError "{old}: does not mention {k} (the inventory is wrong)"
    let openT := (← Lean.getConstInfo openN).type
    let closedT := (← Lean.getConstInfo closed).type
    unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
      throwError "{openN}: does not ask MachineClosesAt"
    if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{closed}: still asks MachineClosesAt"
    -- (3) the binders of the closed form: the run and reflections only
    let (nProps, refl) ← Lean.Meta.forallTelescope closedT fun xs _ => do
      let mut props : Nat := 0
      let mut refl : List Lean.Name := []
      for x in xs do
        let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
        if ← Lean.Meta.isProp t then
          props := props + 1
          if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then pure ()
          else if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
              t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then
            for k in [f, m, rc] do
              if (t.find? fun e => e == Lean.toExpr k).isSome then refl := refl ++ [k]
          else
            throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
      return (props, refl)
    Lean.logInfo m!"NOPORTS SPONGE BINDERS {closed}: {nProps} proposition binders; reflections of {refl}"
    unless nProps == 4 && refl.length == 3 && refl.contains f && refl.contains m &&
        refl.contains rc do
      throwError "{closed}: {nProps} proposition binders, reflections of {refl}; expected the run and one reflection each of {f}, {m}, {rc}"
    -- (4) the reduced boundary and its goal gap: ONE antecedent (ChildBnd), 0 NOT ALLOWED, no gap hypothesis
    let closedB := f ++ `machine_design_noPortsNR1_closedB
    let gap := f ++ `machine_design_noPortsNR1_closedB_gap
    let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
    Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
    Lean.logInfo m!"NOPORTS SPONGE: {f} AS AN ENTRY — GENERATED by the built #machine_no_ports_kids: {openN} and {closed} (closing: {f}.closes_deep, generated under maxRecDepth 1000000) on standard axioms, no statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck or kidsMaskedN, while {old} (generated in this file by the switched #machine_design_svNR, whose loop is the grouped one) asks the four; {closedB}: under the existentials ONE antecedent, ChildBnd, 0 NOT ALLOWED, no gap hypothesis in {gap}. Callee {m}: a register machine with a one-output call of the gate child {rc}. SCOPE: one declaration, a domain-polymorphic parent WITH registers under the general closing, depth 1, data conditions decided per declaration (conditions, not reductions), compiler guards with fallback, DesignSV of the module list — not the SV string, not #sim; the run, the three reflections and ChildBnd stay premises. NOT covered: Keccak's function, keccakF1600HW under its own name, {f} as a child"
