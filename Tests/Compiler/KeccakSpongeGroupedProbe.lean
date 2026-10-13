import Lean.Elab.Command
import IP.Crypto.Keccak256Sponge
import Tools.ShippingMachineCommand
import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingOneOutGenCommand
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineDepthCommandRG
import Tools.ShippingChildIfaceGen
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingBoundaryClose
import Tests.Compiler.KeccakSpongeLogLib

/-! # The sponge's depth endpoint by the GROUPED generator: a LOG-ONLY probe (round par/a-27)

WRITTEN, NOT BUILT, NOT RUN. CLAIMS NOTHING: no step asserts, a failing step
is a `FAILED` line and the environment before it. It runs

    #machine_design_svNRG keccak256SpongeHW 1 as_old

(`Tools/ShippingMachineDepthCommandRG.lean`) after the base commands of
`KeccakSpongeStepProbe2` (steps 2–7, measured there: ≈ 2 min), and — only if
it returns — the commands that build on the depth endpoint.

## Why `as_old`

`#machine_no_ports_kids f n` (`Tools/ShippingNoPortsKidsCommand.lean` 509,
645), and the `noShips` / `noKids` / `noOuts` generators and
`#machine_closes_at`'s closed forms, look the depth endpoint up BY NAME
(`f.machine_ships_hierNR{n}`, `f.machine_design_svNR{n}`) and read the ships
theorem's VALUE (`machine_ships_hierC` applied to 25 arguments). With
`as_old` the grouped command adds `machine_composedNR1` as another name of
`machine_composedNRG1` and lets the OLD `generateDesignNR` build
`machine_ships_hierNR1` / `machine_design_svNR1` from it (old value form);
the `G` names of those two are other names of them. `#machine_closes_deep`
and `#machine_boundary_close` take a declaration / a theorem name and need
no alias.

## Where the lines go

Every step writes `SPG STEP START …` BEFORE it runs and `OK (ms)` / `FAILED
(ms) — message` / `SKIPPED — missing constants` after, to the progress FILE
(`SPARKLE_MACHINE_PROGRESS`, else `.lake/keccak-sponge-grouped.log`), each
line with a millisecond clock and the process's resident / peak memory. The
grouped generator writes its own `progress` lines to the SAME file (only
when the variable is set): per group fact `START`, `proved (ms)`,
`Meta.check (ms)`; per entry `proved and checked (ms)`; `checking` /
`checked` around the kernel's check of the composed theorem; and, with
`SPARKLE_DEPTH_GROUP_KERNEL=1`, each group fact's kernel check ALONE
(`kernel alone START / OK (ms)`; the fact is checked twice then — use it to
find which fact the kernel is slow on, not for the routine run).

## For the integrator

TARGET-ONLY, NEVER IMPORTED, not for `Tests/AllTests.lean`; never together
with `KeccakProbeTest`, `OneOutWKeccakFTest`, `KeccakSpongeStepProbe`,
`KeccakSpongeStepProbe2` (the same constants).

    SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/keccak-sponge-grouped.log \
      ~/sparkle-work/bin/cgrun.sh -n sponge-grouped -m 3G -s 0 -t 2400 -- \
      lake build Tests.Compiler.KeccakSpongeGroupedProbe

(a fresh file each run). With the kernel-alone lines:

    SPARKLE_DEPTH_GROUP_KERNEL=1 SPARKLE_MACHINE_PROGRESS=… (the same command)

## The steps

| step | what | measured before / predicted |
|---|---|---|
| 0a, 0b, 0c | self-tests of the wrapper (FAILED, OK, the variables) | — |
| 1 | reader data of the sponge and `wKeccakF` | 5 + 10 s [M] |
| 2–7 | the base (`#gate_child`, `#machine_endpoint` ×2, `#machine_linked`, `#machine_composed`, `#machine_closes_at`) | ≈ 2 min [M] |
| 8 | `#machine_design_svNRG keccak256SpongeHW 1 as_old` | see `docs/parallel/A-depth-grouped.md` §5 [P] |
| 9 | `#machine_closes_deep keccak256SpongeHW` | not measured |
| 10, 11 | `#machine_design_svHR wKeccakF`, `#machine_oneout wKeccakF` (what step 12 needs of the child) | built in `OneOutWKeccakFTest`, time not recorded here |
| 12 | `#machine_no_ports_kids keccak256SpongeHW 1` | not measured |
| 13 | `#machine_boundary_close …machine_design_noPortsNR1_closed` | not measured |

Steps 9–13 are SKIPPED (a line each) when step 8 left no
`machine_ships_hierNR1`. -/

namespace Tests.Compiler.KeccakSpongeGroupedProbe
open Lean Meta Elab Command

/-- The file the lines go to without the progress variable. -/
def fallback : String := ".lake/keccak-sponge-grouped.log"

/-- A line of the probe: to the progress file now, to the message log when
the command ends. -/
def note (msg : String) : CommandElabM Unit := do
  Tests.Compiler.KeccakSpongeLogLib.toFile fallback msg
  logInfo m!"{msg}"

/-- One step. The FIRST thing it does is write a line to the file: `START`,
or `SKIPPED` with the missing constants. Then the action; `OK (ms)` or
`FAILED (ms) — message` with the environment and the message log put back.
Never throws. (The wrapper of `KeccakSpongeStepProbe2`, restated: that file
cannot be imported, it generates the constants.) -/
def runStep (label : String) (deps : List Name) (act : CommandElabM Unit) :
    CommandElabM Unit := do
  let env0 ← getEnv
  let missing : List Name := deps.filter fun n => !env0.contains n
  unless missing.isEmpty do
    note s!"SPG STEP {label}: SKIPPED — not in the environment: {missing}"
    return
  note s!"SPG STEP START {label}"
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
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    note s!"SPG STEP {label}: FAILED ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}"
  | none =>
    let infos ← (msgs.filter (·.severity == .information)).mapM fun m => m.data.toString
    for i in infos do
      Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"  | {Tests.Compiler.KeccakSpongeLogLib.clipStr i 3000}"
    note s!"SPG STEP {label}: OK ({t1 - t0} ms)"

/-- `#spg_cmd "n" "what" given [c, …] in cmd`: a command as a step. -/
elab "#spg_cmd " step:str ppSpace tag:str " given " "[" ids:ident,* "]" " in " c:command :
    command => do
  let deps : List Name := ids.getElems.toList.map fun i => i.getId
  runStep s!"{step.getString} {tag.getString}" deps (elabCommand c)

/-- `#spg_env "n"`: which of the two variables are set. -/
elab "#spg_env " step:str : command => do
  let isSet ← Tests.Compiler.KeccakSpongeLogLib.progressSet
  let kern := (← IO.getEnv "SPARKLE_DEPTH_GROUP_KERNEL").isSome
  note s!"SPG STEP {step.getString} SPARKLE_MACHINE_PROGRESS set: {isSet} (when false the generators write NO progress line and this file's lines are in {fallback}); SPARKLE_DEPTH_GROUP_KERNEL set: {kern} (when true each group fact is also checked by the kernel alone, with its own line)"

/-- `#spg_read "n" [decl, …]`: the reader's data (logged, nothing asserted). -/
elab "#spg_read " step:str " [" ids:ident,* "]" : command => do
  for i in ids.getElems do
    let n := i.getId
    runStep s!"{step.getString} read {n}" [n] do
      let r ← liftTermElabM (Tools.ShippingMachineCommand.readMachine n)
      note s!"  {Tests.Compiler.KeccakSpongeLogLib.describeRead r}"

/-- `#spg_summary [c, …]`: which of the named constants exist at the end. -/
elab "#spg_summary " "[" ids:ident,* "]" : command => do
  let env ← getEnv
  let names : List Name := ids.getElems.toList.map fun i => i.getId
  let present : List Name := names.filter fun n => env.contains n
  let absent : List Name := names.filter fun n => !env.contains n
  note s!"SPG STEP END: in the environment {present}; NOT in the environment {absent}. LOG ONLY — nothing here is asserted"

end Tests.Compiler.KeccakSpongeGroupedProbe

/-! ## Step 0: the wrapper itself -/

#spg_cmd "0a" "self-test of the wrapper (FAILED is the expected line: an unknown constant)"
    given [Nat] in
  #check keccakSpongeGroupedNoSuchConstant

#spg_cmd "0b" "self-test of the wrapper (OK is the expected line)" given [Nat] in
  #check Nat

#spg_env "0c"

/-! ## Step 1: the reader's data -/

set_option maxHeartbeats 0 in
#spg_read "1" [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF]

/-! ## Steps 2–7: the base (as `KeccakSpongeStepProbe2`) -/

set_option maxHeartbeats 0 in
#spg_cmd "2" "keccakRcHW #gate_child" given [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW] in
  #gate_child Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

set_option maxHeartbeats 0 in
#spg_cmd "3" "wKeccakF #machine_endpoint" given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#spg_cmd "4" "wKeccakF #machine_linked"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_linked Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#spg_cmd "5" "wKeccakF #machine_composed"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_linked,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_composed Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#spg_cmd "6" "keccak256SpongeHW #machine_endpoint"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

set_option maxHeartbeats 0 in
#spg_cmd "7" "wKeccakF #machine_closes_at"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_closes_at Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

/-! ## Step 8: the grouped depth endpoint, the old names added -/

set_option maxHeartbeats 0 in
#spg_cmd "8" "keccak256SpongeHW #machine_design_svNRG 1 as_old"
    given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at] in
  #machine_design_svNRG Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1 as_old

/-! ## Steps 9–13: what builds on the depth endpoint (only if step 8 returned) -/

set_option maxHeartbeats 0 in
#spg_cmd "9" "keccak256SpongeHW #machine_closes_deep"
    given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at] in
  #machine_closes_deep Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

set_option maxHeartbeats 0 in
#spg_cmd "10" "wKeccakF #machine_design_svHR"
    given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_linked] in
  #machine_design_svHR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#spg_cmd "11" "wKeccakF #machine_oneout"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svHR,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at] in
  #machine_oneout Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#spg_cmd "12" "keccak256SpongeHW #machine_no_ports_kids 1"
    given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.closes_deep,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.oneout_callsOk,
      Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_portsRawH] in
  #machine_no_ports_kids Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1

set_option maxHeartbeats 0 in
#spg_cmd "13" "keccak256SpongeHW #machine_boundary_close"
    given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed] in
  #machine_boundary_close
    Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed

/-! ## What exists at the end -/

#spg_summary [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedRA,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedNRH0,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNRG1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNRG1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_svNRG1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_svNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.closes_deep,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.closes_deep,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_design_svHR,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.oneout_callsOk,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closed,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_noPortsNR1_closedB]
