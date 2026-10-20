import IP.Crypto.Keccak256Sponge
import Tools.ShippingMachineCommand
import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingOneOutGenCommand
import Tools.ShippingFinalGoalCommand
import Tests.Compiler.OneOutFamilyTest
import Tests.Compiler.KeccakSpongeLogLib

/-! # `#machine_oneout` on `wKeccakF`: the Keccak-f[1600] permutation AS AN ENTRY (G1, round par/a-25)

WRITTEN, NOT BUILT. Modelled on `Tests/Compiler/OneOutMidHTest.lean` (BUILT):
no new theorem is written in this file, BUILT commands are run on one more
declaration and the family audit of `Tests/Compiler/OneOutFamilyTest.lean`
(BUILT) is applied to what they leave.

`wKeccakF` (`IP/Crypto/Keccak256Sponge.lean` 82–91) is the
`@[hardware_module]` wrapper of `keccakF1600HW` (`IP/Crypto/Keccak256HW.lean`
168–339): its value is the application `keccakF1600HW start in0 … in24`, read
through its core. The reader's data, as the log-only probe
`Tests/Compiler/KeccakProbeTest.lean` printed them (run record of
`docs/parallel/B-keccak.md`, step 3): `nDecl = 27` (the domain binder,
`start : Bool`, 25 lanes of 64 bits), 124 binders, 27 registers (25 × 64, 5,
1 = 1606 state bits), 69 hardware `let`s, ONE call entry — the gate child
`keccakRcHW` (`BitVec 5 → BitVec 64`, a 32-entry table) with the argument
`let` 42 —, `instFields = []` (the ONE-OUTPUT closing), 27 outputs (`l0 … l24`
of 64 bits, `round` of 5, `done` of 1). That is `midH`'s class (a parent WITH
a register, one gate child, the one-output closing); new against `midH`: a
wrapper entry, 27 outputs, 26 hardware inputs, 1606 state bits.

## For the integrator: HEAVY — TARGET-ONLY, not for `Tests/AllTests.lean` (recommendation)

    lake build Tests.Compiler.OneOutWKeccakFTest

What was measured (the probe's run `20261013-080244-keccak-probe`, steps
5–8 and 10–12 — the commands of this file, in this order): 5.3 + 23.0 + 13.8
+ 13.5 + 12.8 + 33.1 + 19.9 s ≈ 2 min of generation, plus two reader runs of
≈ 10 s each and the audit (not measured). The process's VmHWM was 2.32 GB,
but 1.83 GB of that was there at the probe's step 0a, before any Keccak
command: the mapped `.olean` files of the imports. The cgroup's own
`memory.current` (the number the 3 GiB cap is about) was 0.73–0.85 GB over
the whole of steps 0–12 (`samples.txt` of that run, t = 60 … 320 s).

Why target-only all the same:

1. `cgrun.sh -j N` only exports `LEAN_NUM_THREADS=N` (default 2; line 87 of
   `~/sparkle-work/bin/cgrun.sh`); lake takes its job parallelism from the
   same task pool, so with the default TWO `lean` processes run at once: 119
   of the 800 saved run records have `max_concurrent_lean=2`, all with
   `threads=2`. The peak is therefore NOT per-file-and-sequential in an
   `AllTests` build: this file's ≈ 0.8 GB (charged) would sit next to another
   test's.
2. That 0.8 GB is the charge with a WARM page cache (the oleans were mapped
   by earlier runs and charged elsewhere). On a cold cache the 1.8 GB of
   mapped oleans are charged to the build's cgroup as reclaimable file
   pages: with swap 0 they can be reclaimed, but the build then runs at
   `memory.high` (throttled), as the sponge step of the probe did.
3. ≈ 3 minutes on every rebuild of any imported `Tools.*` generator, for ONE
   declaration.
4. Nothing of it is imported by another test (the sponge's chain does not
   end yet, `docs/parallel/A-keccak.md`).

If it is wanted in `AllTests` later: build it once as a target under
`cgrun.sh -m 3G -s 0 -j 1` with a cold cache, read `memory_peak_file` of the
record, and decide on that number — not on VmHWM.

NAME CLASH: this file ADDS `keccakRcHW.gate_*`, `wKeccakF.machine_sound`,
`.machine_linked`, `.machine_composed`, `.machine_closes_at`,
`.machine_design_svHR`, `.machine_design_svH_full(_closed)`, `.oneout_*`, ….
`Tests/Compiler/KeccakProbeTest.lean` and
`Tests/Compiler/KeccakSpongeStepProbe.lean` add the same constants: NEVER
import this file together with either (all three are target-only; the first
`run_cmd` below throws when the constants are already there).

## EXPECTED (stated before the build; the command THROWS on another class)

    ONEOUT WKECCAKF DATA …wKeccakF: nDecl=27; … slots=27 … (1606 state bits); lets=69; … call entries=1 …
    ONEOUT GEN …wKeccakF: GENERATED [wKeccakF.machine_design_svH_full, wKeccakF.machine_design_svH_full_closed] — …
    ONEOUT FULL PREMISE …_closed: run        | binder hr : RunsTo (synthesizeCombinational `wKeccakF) …
    ONEOUT FULL PREMISE …_closed: reflection | binder entry : MachineDefines … `wKeccakF wKeccakF.machineData.shape
    ONEOUT FULL PREMISE …_closed: reflection | binder hR0 : EntryDefines … `keccakRcHW keccakRcHW.gateValue
    ONEOUT FULL PREMISE …_closed: ChildBnd   | antecedent under the existentials : ChildBnd mref cref w
    ONEOUT FULL PREMISE …_closed: reflection | antecedent under the existentials : EntryDefines … `keccakRcHW keccakRcHW.gateValue
    GOALGAP wKeccakF.machine_design_svH_full_closed_gap … (none NOT ALLOWED)
    ONEOUT FAMILY wKeccakF: … other: NONE …
    ONEOUT WKECCAKF: …

What the probe showed and what it did not: the seven commands returned OK
and the probe's own premise listing of the open and the closed form had 4
lines each (run, `MachineDefines wKeccakF`, `EntryDefines keccakRcHW`, and
the open form's closing premise / the closed form's antecedent). NOT run on
`wKeccakF` before this file: `#machine_oneout_try` (the class assertion),
the family audit — standard axioms of every generated constant, the checker
inventory (`refuse`, `mentioned`, `hidden`), the premise classification with
`other` = NONE on the closed form, the goal-gap reporter.

| endpoint | premise of `wKeccakF.machine_design_svHR` | predicted state |
|---|---|---|
| `wKeccakF.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck D.modules b` | WRITTEN, NOT BUILT — predicted absent (the generator returned GENERATED once, inside the log-only probe; nothing was kept, nothing audited) |
| | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt wKeccakF` (open form) | predicted absent in `_closed` (`wKeccakF.machine_closes_at`), pending build |
| | `hr`, `MachineDefines wKeccakF`, `EntryDefines keccakRcHW`, `ChildBnd` | run boundary: they stay premises |

## SCOPE (binding for any report)

ONE declaration, `wKeccakF`, AS AN ENTRY: a parent WITH registers, one gate
child (`keccakRcHW`), the one-output closing, depth 0. Data conditions
decided per declaration by the kernel (`wKeccakF.oneout_*`,
`keccakRcHW.gate_width`, what `#gate_child` left) are conditions, not
reductions; the run, `MachineDefines wKeccakF`, `EntryDefines keccakRcHW`,
`ChildBnd` stay premises (no runtime model); the result depends on the
compiler's guards with fallback; the conclusion is about `DesignSV (childMap
D.modules) 0 (checkedOptimize b)` — the module list, not the SV string, not
`#sim`.

NOT covered, and NOT implied by this endpoint: `wKeccakF` AS A CHILD — the
sponge `keccak256SpongeHW` (its depth endpoint `#machine_design_svNR … 1`
did not return within the probe's limit; `docs/parallel/A-keccak.md`);
`keccakF1600HW` under its own name (the plain `def` is not an entry here);
any statement about Keccak's FUNCTION (this is the compiler's correctness on
one declaration, not that the declaration computes Keccak-f).

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The reader's data: LOGGED first (nothing asserted about the shape here) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF
  let rc := ``Sparkle.IP.Crypto.Keccak256HW.keccakRcHW
  let env ← Lean.getEnv
  unless env.contains f do throwError "{f}: not in the environment (a wrong NAME in this file)"
  unless env.contains rc do throwError "{rc}: not in the environment (a wrong NAME in this file)"
  let r ← Tools.ShippingMachineCommand.readMachine f
  Lean.logInfo m!"ONEOUT WKECCAKF DATA {f}: {Tests.Compiler.KeccakSpongeLogLib.describeRead r}"
  let g ← Tools.ShippingMachineCommand.readMachine rc (allowGate := true)
  Lean.logInfo m!"ONEOUT WKECCAKF DATA {rc} (read as a gate-route child's source function): {Tests.Compiler.KeccakSpongeLogLib.describeRead g}"
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [rc ++ `gate_peel, rc ++ `gate_linked, rc ++ `gateValue, f ++ `machineData,
      f ++ `machine_sound, f ++ `machine_linked, f ++ `machine_composed, f ++ `machine_closes_at,
      f ++ `machine_design_svHR, f ++ `machine_design_svH_full, f ++ `oneout_callsOk] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"ONEOUT WKECCAKF DATA: in the environment before the commands: {have_}; not: {lack}"
  -- the name clash of the header: nothing of the chain may exist yet
  unless have_.isEmpty do
    throwError "{have_}: exist already — a Keccak probe (or another generator of the same constants) is imported (NAME CLASH, see the header)"

/-! ## The base endpoints, by the BUILT commands, in the order the probe used (its steps 5–8, 10, 11) -/

set_option maxHeartbeats 0 in
#gate_child Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#machine_linked Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#machine_composed Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

/-! ## The generator (the probe's step 12), with its outcome's class asserted -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF "GENERATED"

/-! ## The family audit: premise lists, checker inventory, standard axioms, goal gap

`Tests.Compiler.OneOutFamilyTest.audit` (BUILT; the `run_cmd` body of the
family test and of `OneOutMidHTest`): throws unless `other` is exactly the
closing premise on the open form and NONE on the closed form, none of
`shipsHierHCheck`, `kidsComb`, `designCheck`, `outsCheck` (nor the four
residual checkers) is written in either statement or hidden in a premise's
definition, every generated constant is on the standard axioms, and the
goal-gap reporter lists no NOT ALLOWED premise of the closed form. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF
    [``Sparkle.IP.Crypto.Keccak256HW.keccakRcHW] false

/-! ## The scope facts this file relies on, asserted on the reader's data

An error here means the READING of the header is wrong (the declaration is
not the shape it says), independently of the generator's outcome. The data
were logged by the first `run_cmd`. -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF
  let rc := ``Sparkle.IP.Crypto.Keccak256HW.keccakRcHW
  let r ← Tools.ShippingMachineCommand.readMachine f
  let outNames : List String := r.shape.layout.outs.map (·.name)
  let slotWs : List Nat := r.shape.layout.slots.map (·.width)
  let stateBits : Nat := slotWs.foldl (fun a w => a + w) 0
  let lanes : List String := (List.range 25).map fun i => s!"l{i}"
  unless r.shape.insts.map (·.1) == [rc] do
    throwError "{f}: the call entries are {r.shape.insts.map (·.1)}, expected [{rc}]"
  unless r.shape.instFields.isEmpty do
    throwError "{f}: instFields = {r.shape.instFields} — not the one-output closing"
  unless r.shape.layout.slots.length == 27 && stateBits == 1606 do
    throwError "{f}: {r.shape.layout.slots.length} registers of {stateBits} bits, expected 27 of 1606"
  unless r.nDecl == 27 do
    throwError "{f}: nDecl = {r.nDecl}, expected 27 (the domain binder, start, 25 lanes)"
  unless outNames == lanes ++ ["round", "done"] do
    throwError "{f}: the outputs are {outNames}, expected l0 … l24, round, done"
  unless (← Lean.getEnv).contains (rc ++ `gate_peel) do
    throwError "{rc}: no gate_peel — not a gate child with #gate_child data"
  let full := f ++ `machine_design_svH_full
  let closed := f ++ `machine_design_svH_full_closed
  let old := f ++ `machine_design_svHR
  unless (← Lean.getEnv).contains full && (← Lean.getEnv).contains closed do
    throwError "{full} / {closed}: not in the environment after #machine_oneout_try (class GENERATED)"
  Lean.logInfo m!"ONEOUT WKECCAKF: {f} — nDecl={r.nDecl}, slots={r.shape.layout.slots.length} ({stateBits} state bits), lets={r.shape.layout.lets}, call entries [{rc}] (gate child), instFields=[], {outNames.length} outputs: a wrapper entry WITH registers, the one-output closing. The endpoint {full} and its closed form {closed} are in the environment; the audit above printed their complete premise lists and threw on none: none of the four check premises of {old} (shipsHierHCheck, kidsComb, designCheck, outsCheck), class other NONE on the closed form, standard axioms. SCOPE: ONE declaration, {f} AS AN ENTRY, depth 0; data conditions decided per declaration by the kernel are conditions, not reductions; the run, MachineDefines of {f}, EntryDefines of {rc} and ChildBnd stay premises; the result depends on the compiler's guards with fallback; the conclusion is DesignSV of the module list — not the SV string, not #sim. NOT covered: {f} as a child (the sponge keccak256SpongeHW), keccakF1600HW under its own name, Keccak's function."
