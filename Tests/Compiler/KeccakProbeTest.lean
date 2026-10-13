import IP.Crypto.Keccak256Sponge
import Tools.ShippingMachineCommand
import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingOneOutGenCommand
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingChildIfaceGen
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingBoundaryClose
import Tools.ShippingFinalGoalCommand

/-! # Keccak: a LOG-ONLY, TIME-LIMITED probe of the built generators (round par/b-18)

WRITTEN, NOT BUILT, NOT RUN. This file CLAIMS NOTHING: no step asserts, no
step throws. It measures which BUILT generator accepts which Keccak
declaration and where the first refusal / failure / timeout is. Reading,
shapes, predictions and "what a result means": `docs/parallel/B-keccak.md`.

## For the integrator

* TARGET-ONLY, NEVER IMPORTED, NOT for `Tests/AllTests.lean`. A step that
  succeeds leaves constants under the declarations' usual names in THIS
  module only (`wKeccakF.machine_sound`, `keccakRcHW.gate_child`,
  `keccak256SpongeHW.machine_design_svNR1`, …). A later proper test must
  generate them itself and must not import this file.
* Run it with a WALL-CLOCK limit and the memory cap, and name a progress
  file:

      SPARKLE_MACHINE_PROGRESS=/abs/path/keccak-progress.log \
        lake build Tests.Compiler.KeccakProbeTest

  (`SPARKLE_*` is on `cgrun.sh`'s environment allow-list.) EVERY line of this
  probe is written to that file AT ONCE, with a millisecond clock and the
  resident / peak memory, and so are the generators' own `progress` lines
  (`Tools.ShippingMachineCommand.progress`, the same variable). Without the
  variable the probe's lines go to `.lake/keccak-probe.log` (the generators'
  lines are then not written). The message log of the build shows a
  command's lines only when the command ENDS, and nothing of a killed build:
  after a timeout READ THE PROGRESS FILE.
* Each step writes `KECCAK PROBE START <n> <what>` BEFORE it starts and
  `KECCAK PROBE <n> <what>: OK | FAILED — <message> | SKIPPED — <missing>`
  when it ends. A timeout / OOM kill inside step N: the file's last line is
  `START N …` (followed by the generator's progress lines); steps < N are
  complete in the file. Steps are ordered by dependency and, within that,
  by increasing expected cost.
* A FAILED step puts the environment and the message log back (nothing of
  it stays). A step whose prerequisites an earlier step did not leave is
  SKIPPED (not run again through a later generator's own recursion).
* What a `try` cannot catch: a stack overflow of the Lean process, an OOM
  kill, the wall-clock kill. Those end the file at the `START` line.

## What may fail in THIS FILE ITSELF (not a Keccak result)

Steps 0a / 0b are a SELF-TEST of the wrapper: 0a must log `FAILED` (an
unknown constant), 0b must log `OK`. If the build stops BEFORE the line
`KECCAK PROBE 0b …: OK` exists, the failure is in this file's own
definitions (the four `elab`s, `describeRead`, `premiseLines`), not in Keccak.
A `SKIPPED — not in the environment` at steps 1–4 means a wrong NAME in this
file. The names were checked by reading the `namespace` lines:
`Sparkle.IP.Crypto.Keccak256HW` (`IP/Crypto/Keccak256HW.lean` 30:
`keccakRcHW` 42, `keccakF1600HW` 168) and `Sparkle.IP.Crypto.Keccak256Sponge`
(`IP/Crypto/Keccak256Sponge.lean` 51: `wKeccakF` 82, `keccak256SpongeHW` 94).

## The steps

| step | command | on |
|---|---|---|
| 0a, 0b | self-test of the wrapper | — |
| 1–4 | `readMachine` (the reader's data) | `keccakRcHW`, `keccakF1600HW`, `wKeccakF`, `keccak256SpongeHW` |
| 5 | `#gate_child` | `keccakRcHW` |
| 6 | `#machine_endpoint` | `wKeccakF` |
| 7 | `#machine_linked` | `wKeccakF` |
| 8 | `#machine_composed` | `wKeccakF` |
| 9 | `#machine_endpoint` | `keccak256SpongeHW` |
| 10 | `#machine_closes_at` | `wKeccakF` |
| 11 | `#machine_design_svHR` | `wKeccakF` |
| 12 | `#machine_oneout` | `wKeccakF` |
| 13 | `#machine_design_svNR … 1` | `keccak256SpongeHW` |
| 14 | `#machine_closes_deep` | `keccak256SpongeHW` |
| 15 | `#machine_no_ports_kids … 1` | `keccak256SpongeHW` |
| 16 | `#machine_boundary_close` | `keccak256SpongeHW.machine_design_noPortsNR1_closed` |

Steps 1–9 are the base (reader, then the base commands leaf first); 10–16
are the check-free generators of the shape (`mid2 → midH → rcH`,
`Tests/Compiler/NoPortsKidsMid2Test.lean`, is the built model of
`keccak256SpongeHW → wKeccakF → keccakRcHW`), each only if what it builds on
exists. After each step the proposition premises of what it generated are
logged (`KECCAK PROBE PREMISES <theorem>`: `ALLOWED` / `NOT ALLOWED` lines
by `Tools.ShippingFinalGoalCommand.allowed` / `analyse`; no constant is
added for that).

Options: `maxHeartbeats 0` on every step, as the built tests set it on
these commands (`ShippingMachineDepthHTest` 43–54, `ShippingChildBoundaryTest`
349, `ShippingCallsCloseTest` 78, `OneOutMidHTest` 90, `NoPortsKidsMid2Test`);
`maxRecDepth 1000000` on step 15 only, as `NoPortsKidsMid2Test` sets it on
`#machine_no_ports_kids` (the `#machine_design_sv*R` commands raise it
themselves). -/

namespace Tests.Compiler.KeccakProbeTest
open Lean Meta Elab Command

/-- A long message, cut. -/
def clipStr (s : String) (n : Nat := 2000) : String :=
  if s.length ≤ n then s
  else (s.toList.take n).foldl (fun acc c => acc.push c) "" ++ " …[clipped]"

/-- One line to the progress file, at once (never fails). -/
def probeToFile (msg : String) : IO Unit := do
  try
    let path := (← IO.getEnv "SPARKLE_MACHINE_PROGRESS").getD ".lake/keccak-probe.log"
    let status ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
    let rss := (status.splitOn "\n").find? (·.startsWith "VmRSS") |>.getD ""
    let hwm := (status.splitOn "\n").find? (·.startsWith "VmHWM") |>.getD ""
    let now ← IO.monoMsNow
    let h ← IO.FS.Handle.mk path IO.FS.Mode.append
    h.putStrLn s!"{now} {msg} [{rss}] [{hwm}]"
    h.flush
  catch _ => pure ()

/-- A line of the probe: to the progress file now, to the message log when
the command ends. -/
def probeNote (msg : String) : CommandElabM Unit := do
  probeToFile msg
  logInfo m!"{msg}"

def binderKindStr (b : Sparkle.Compiler.Elab.MixedGateBinder) : String :=
  match b with
  | Sparkle.Compiler.Elab.MixedGateBinder.domain => "domain"
  | Sparkle.Compiler.Elab.MixedGateBinder.bool => "bool"
  | Sparkle.Compiler.Elab.MixedGateBinder.bits w => s!"bits {w}"

/-- The reader's data of a declaration, as one line. -/
def describeRead (r : Tools.ShippingMachineCommand.Read) : String :=
  let sh := r.shape
  let declKinds : List String := (sh.binders.take r.nDecl).map fun b => binderKindStr b.2
  let slotWs : List Nat := sh.layout.slots.map fun s => s.width
  let stateBits : Nat := slotWs.foldl (fun a w => a + w) 0
  let outs : List String := sh.layout.outs.map fun o => s!"{o.name}:{o.width}"
  let callees : List Name := (sh.insts.map fun i => i.1).eraseDups
  let groups : List (Name × List Nat) := (sh.insts.map fun i => (i.1, i.2.1)).eraseDups
  let groupStrs : List String := groups.map fun g => s!"{g.1} with argument lets {g.2}"
  let results : List String := sh.insts.map fun i => binderKindStr i.2.2
  s!"nDecl={r.nDecl}; declared binders {declKinds}; binders={sh.binders.length}; slots={sh.layout.slots.length} of widths {slotWs} ({stateBits} state bits); lets={sh.layout.lets}; runs={sh.runs}; loops={sh.loops}; rootLets={r.rootLets}; hasOuter={r.hasOuter}; nested={r.nested}; call entries={sh.insts.length} with result kinds {results}; distinct callees {callees}; distinct (callee, argument lets) groups ({groups.length}): {groupStrs}; instFields ({sh.instFields.length}): {sh.instFields}; outputs ({sh.layout.outs.length}): {outs}; outNames {r.outNames}; tuple result: {r.tuple.isSome}"

/-- One reading step: the machine reader, and where it refuses, the reading
of a gate-route child's source function (`allowGate`). -/
def readStep (step : Nat) (n : Name) : CommandElabM Unit := do
  unless (← getEnv).contains n do
    probeNote s!"KECCAK PROBE {step} read {n}: SKIPPED — not in the environment (a wrong NAME in the probe file, not a Keccak result)"
    return
  probeNote s!"KECCAK PROBE START {step} read {n}"
  let t0 ← IO.monoMsNow
  let r? : Except String Tools.ShippingMachineCommand.Read ← try
      pure (Except.ok (← liftTermElabM (Tools.ShippingMachineCommand.readMachine n)))
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  let t1 ← IO.monoMsNow
  match r? with
  | Except.ok r =>
    probeNote s!"KECCAK PROBE {step} read {n}: OK ({t1 - t0} ms) — the MACHINE route reads it. {describeRead r}"
  | Except.error msg =>
    probeNote s!"KECCAK PROBE {step} read {n}: FAILED ({t1 - t0} ms) — the machine reader refuses it: {clipStr msg}"
    probeNote s!"KECCAK PROBE START {step} read {n} (allowGate)"
    let g? : Except String Tools.ShippingMachineCommand.Read ← try
        pure (Except.ok (← liftTermElabM
          (Tools.ShippingMachineCommand.readMachine n (allowGate := true))))
      catch ex =>
        let msg2 ← ex.toMessageData.toString
        pure (Except.error msg2)
    let t2 ← IO.monoMsNow
    match g? with
    | Except.ok r =>
      probeNote s!"KECCAK PROBE {step} read {n} (allowGate): OK ({t2 - t1} ms) — read as a gate-route child's source function. {describeRead r}"
    | Except.error msg2 =>
      probeNote s!"KECCAK PROBE {step} read {n} (allowGate): FAILED ({t2 - t1} ms) — {clipStr msg2}"

/-- The proposition premises of a generated theorem: its proposition binders
and, where its conclusion is `∃ …, P ∧ (A₁ → … → C)`, the antecedents `Aᵢ`,
each classified by the goal-gap classifier. Adds no constant. -/
def premiseLines (thm : Name) : MetaM (Array String) := do
  unless (← getEnv).contains thm do
    return #[s!"ABSENT {thm}"]
  let info ← getConstInfo thm
  forallTelescope info.type fun xs body => do
    let mut out : Array String := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        let tag : String :=
          if Tools.ShippingFinalGoalCommand.allowed t then "ALLOWED     binder"
          else "NOT ALLOWED binder"
        let pp ← ppExpr t
        out := out.push s!"{tag}: {clipStr (toString pp) 700}"
    let inner : Array String ← try
        let antes ← Tools.ShippingFinalGoalCommand.analyse body #[]
        pure (antes.map fun a => clipStr a.line 700)
      catch _ =>
        pure #["(the conclusion is not of the form ∃ …, P ∧ (A → …): no antecedent read under an existential)"]
    return out ++ inner

/-- `#keccak_read n decl`: step `n`, the reader's data of `decl`. -/
elab "#keccak_read " step:num ppSpace d:ident : command => do
  readStep step.getNat d.getId

/-- `#keccak_premises [thm, …]`: the premises of each theorem that exists. -/
elab "#keccak_premises " "[" ids:ident,* "]" : command => do
  for i in ids.getElems do
    let n := i.getId
    let lines : Array String ← try
        liftTermElabM (premiseLines n)
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure #[s!"the premise listing failed: {clipStr msg}"]
    probeNote s!"KECCAK PROBE PREMISES {n} ({lines.size} lines):\n{String.intercalate "\n" lines.toList}"

/-- `#keccak_probe n "what" needs [c, …] in cmd`: step `n`. SKIPPED when a
named constant is not in the environment; else `START` is written, `cmd` is
elaborated, and `OK` or `FAILED — message` is written. On a failure (thrown,
or an error in the message log) the environment and the message log are put
back. -/
elab "#keccak_probe " step:str ppSpace tag:str " needs " "[" ids:ident,* "]" " in " c:command :
    command => do
  let label : String := s!"{step.getString} {tag.getString}"
  let env0 ← getEnv
  let missing : List Name :=
    (ids.getElems.toList.map fun i => i.getId).filter fun n => !env0.contains n
  unless missing.isEmpty do
    probeNote s!"KECCAK PROBE {label}: SKIPPED — not in the environment: {missing}"
    return
  probeNote s!"KECCAK PROBE START {label}"
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let t0 ← IO.monoMsNow
  let thrown : Option String ← try
      elabCommand c
      pure none
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (some msg)
  let t1 ← IO.monoMsNow
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match thrown with
    | some msg => some msg
    | none => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  match failure with
  | some msg =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    probeNote s!"KECCAK PROBE {label}: FAILED ({t1 - t0} ms) — {clipStr msg}"
  | none =>
    -- the command's own lines, to the progress file too
    let infos ← (msgs.filter (·.severity == .information)).mapM fun m => m.data.toString
    for i in infos do
      probeToFile s!"  | {clipStr i 3000}"
    probeNote s!"KECCAK PROBE {label}: OK ({t1 - t0} ms)"

/-- `#keccak_summary [c, …]`: which of the named constants exist at the end. -/
elab "#keccak_summary " "[" ids:ident,* "]" : command => do
  let env ← getEnv
  let names : List Name := ids.getElems.toList.map fun i => i.getId
  let present : List Name := names.filter fun n => env.contains n
  let absent : List Name := names.filter fun n => !env.contains n
  probeNote s!"KECCAK PROBE END: in the environment {present}; NOT in the environment {absent}. LOG ONLY — nothing here is asserted; a constant present here exists in THIS target-only module and nowhere else"

end Tests.Compiler.KeccakProbeTest

/-! ## Step 0: the wrapper itself (0a must be FAILED, 0b must be OK) -/

#keccak_probe "0a" "self-test of the wrapper (FAILED is the expected line: an unknown constant)"
    needs [Nat] in
  #check keccakProbeNoSuchConstant

#keccak_probe "0b" "self-test of the wrapper (OK is the expected line)" needs [Nat] in
  #check Nat

/-! ## Steps 1–4: the reader's data -/

set_option maxHeartbeats 0 in
#keccak_read 1 Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

set_option maxHeartbeats 0 in
#keccak_read 2 Sparkle.IP.Crypto.Keccak256HW.keccakF1600HW

set_option maxHeartbeats 0 in
#keccak_read 3 Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#keccak_read 4 Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

/-! ## Steps 5–9: the base commands, leaf first -/

set_option maxHeartbeats 0 in
#keccak_probe "5" "keccakRcHW #gate_child" needs [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW] in
  #gate_child Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

#keccak_premises [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child]

set_option maxHeartbeats 0 in
#keccak_probe "6" "wKeccakF #machine_endpoint"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_ships,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_ships_wired]

set_option maxHeartbeats 0 in
#keccak_probe "7" "wKeccakF #machine_linked"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_linked Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_linked]

set_option maxHeartbeats 0 in
#keccak_probe "8" "wKeccakF #machine_composed"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_linked,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_composed Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composed]

set_option maxHeartbeats 0 in
#keccak_probe "9" "keccak256SpongeHW #machine_endpoint"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_wired]

/-! ## Steps 10–12: the check-free chain of `wKeccakF` as an entry (the `midH` chain) -/

set_option maxHeartbeats 0 in
#keccak_probe "10" "wKeccakF #machine_closes_at"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_closes_at Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

set_option maxHeartbeats 0 in
#keccak_probe "11" "wKeccakF #machine_design_svHR"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_linked] in
  #machine_design_svHR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svHR]

set_option maxHeartbeats 0 in
#keccak_probe "12" "wKeccakF #machine_oneout"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svHR,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at] in
  #machine_oneout Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full_closed]

/-! ## Steps 13–16: the check-free chain of the sponge as an entry (the `mid2` chain) -/

set_option maxHeartbeats 0 in
#keccak_probe "13" "keccak256SpongeHW #machine_design_svNR 1"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at] in
  #machine_design_svNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_svNR1]

set_option maxHeartbeats 0 in
#keccak_probe "14" "keccak256SpongeHW #machine_closes_deep"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at] in
  #machine_closes_deep Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.closes_deep,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.closes_deep]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#keccak_probe "15" "keccak256SpongeHW #machine_no_ports_kids 1"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.closes_deep,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.oneout_callsOk,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_portsRawH] in
  #machine_no_ports_kids Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed]

set_option maxHeartbeats 0 in
#keccak_probe "16" "keccak256SpongeHW #machine_boundary_close"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed] in
  #machine_boundary_close
    Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed

#keccak_premises [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closedB]

/-! ## What exists at the end -/

#keccak_summary [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child,
  Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_linked,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_ships_wired,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_linked,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composed,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svHR,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svH_full_closed,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.closes_deep,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_wired,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_svNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.closes_deep,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closedB]
