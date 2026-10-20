# Depth switch: the old-loop comparison — RECORD (kept after the temporary files are removed)

Written on `par/b-28` (from poc `d71fd052`), 2026-10-13, before the deletion of
`Tools/ShippingMachineDepthCommandROld.lean` and `Tests/Compiler/DepthSwitchTypeTest.lean`.
Reviewer ruling 2026-10-13, item 6: "The old-loop comparison evidence is accepted. After
de-duplicating RG the temporary old file may be removed, but keep as a RECORD the head list, the 51
targets, the comparison result and the version; keep the ordinary regression tests and the final
kernel / axiom checks."

This file is a record of a run that HAS BEEN MADE. It is not a test and nothing re-checks it. Every
quoted line is copied from `docs/parallel/verification-depth-switch.md` (the integrator's record of
that run); nothing here was re-run by the writer of this file.

## 1. Version

| what | value |
|---|---|
| the switch (`#machine_design_svNR` on the grouped loop) | poc `bf32874b` |
| the head table of `generateSeqChildN` (`_of_loop` / `_of_regs`) | poc `f3ee9c57` |
| acceptance commit (the temporary old loop, the type test, the pin table) | poc `77b3ba4f` |
| verified tree | `75f610415713004f3f8de54db7f7d3f141468aae` (= poc 25f68ea2 + par/b-23 56fb2aae + the pin table + one `lean_lib` + three imports in `Tests/AllTests.lean`) |
| the three commits | built TOGETHER as that tree; the two intermediate commits were not built separately |
| pin table recorded on | poc `25f68ea2` (the two generator files byte-identical to `edd9496c` there), run `20261013-144930-pin-record` |
| environment | cgrun 3 GiB, swap 0, one job; GitHub CI: 0 runs for that HEAD — no CI result is claimed |

Run ids (from `verification-depth-switch.md`, "Runs"):

| run id | command | result |
|---|---|---|
| `20261013-144930-pin-record` | `env DEPTH_PIN_MODE=record lake build Tests.Compiler.DepthSwitchPinTest` | exit 1 ON PURPOSE (record mode prints the table and throws) |
| `20261013-144953-switch-1` | `lake build Tools.ShippingMachineDepthCommandR Tools.ShippingMachineDepthCommandRG Tools.ShippingMachineDepthCommandROld Tests.Compiler.DepthSwitchTypeTest Tests.Compiler.DepthSwitchPinTest Tests.Compiler.DepthGroupedFamilyTest Tests.Compiler.DepthLoopChildTest Tests.Compiler.DepthLoopChildCompareTest` | exit 1: the integrator's first paste of the pin table left a stray `]`, which failed `DepthSwitchPinTest` alone; removed before the next runs |
| `20261013-145604-switch-all` | `lake build Tests.AllTests Tests.Compiler.DepthGroupedFamilyTest Tests.Compiler.DepthLoopChildTest` | success, `Build completed successfully (1267 jobs).` |
| `20261013-145818-switch-wk` | `lake build Tests.Compiler.OneOutWKeccakFTest` | success (568 jobs) |
| `20261013-150059-switch-sponge` | `lake build Tests.Compiler.NoPortsKeccakSpongeTest` | success (583 jobs) |
| `20261013-151138-switch-sponge-direct` | `lake build Tests.Compiler.DepthSwitchSpongeTest` | success (569 jobs) |

## 2. Where the old loop's source is

`Tools/ShippingMachineDepthCommandROld.lean` and `Tests/Compiler/DepthSwitchTypeTest.lean` are
removed on `par/b-28`. Both are recoverable from git:

| file | at `77b3ba4f` (the tree that was BUILT) | at `d71fd052` (last commit that has it) |
|---|---|---|
| `Tools/ShippingMachineDepthCommandROld.lean` | blob `0ad61ef6a3d49895f94cbfea30af6d6137304cde` | blob `46be63b2fa43e8e9ce1308baac9b349a8326de77` |
| `Tests/Compiler/DepthSwitchTypeTest.lean` | blob `7a52bb84381d7ee49d62f692d6a19fad4d5f76fc` | the same blob |

    git show 77b3ba4f:Tools/ShippingMachineDepthCommandROld.lean
    git show 77b3ba4f:Tests/Compiler/DepthSwitchTypeTest.lean

The two versions of the old-loop file differ in ONE line (commit `c4079676`: `memTactic` takes the
call index; the same one-line change was made in `…CommandR.lean` and `…CommandRG.lean`). The
comparison below is of the `77b3ba4f` text. `AllTests` (which contained `DepthSwitchTypeTest`) was
reported green on later trees too, the last one `da3968872d89ba987dd6cff9235dc3746c6427d4`
(the message of commit `d71fd052`: "Tests.AllTests 1281 jobs green"), so the comparison also ran
with the one-line change on both sides; its log line on those trees is not recorded here.

What the old file was (its own header): `generateCoreNROld` = `generateCoreNR` of
`Tools/ShippingMachineDepthCommandR.lean` at `edd9496c`, lines 185–562 "VERBATIM (assembled by a
script from `git show edd9496c:…`, not retyped)", under the names `f.machine_composedNRO{n}`,
`f.machine_ships_hierNRO{n}`, `f.machine_design_svNRO{n}`, command `#machine_design_svNR_old f n`.
The pre-switch generator itself is `git show edd9496c:Tools/ShippingMachineDepthCommandR.lean`.

## 3. The head list (which trace heads the depth generators accept)

Read from the source at `d71fd052`; the same text as at `77b3ba4f` (only the `memTactic` line
differs).

**A sequential child WITHOUT calls** — `seqChildNProof` (`Tools/ShippingMachineDepthCommand.lean`
46–63), used by `generateSeqChildN`: the head of `c.machine_sound`'s value is mapped to its wired
twin, then `Tools.ShippingMachineDepthRun.seqChildRunN_full` at that twin on the endpoint's
arguments, eight conditions decided.

| head of `c.machine_sound` | wired twin | exercised by |
|---|---|---|
| `Tools.ShippingMachineAuto.machine_trace_of_data` (a `circuit do`) | `Tools.ShippingMachineCausal.machine_traceL_of_data` | the 17 endpoints below (children `cnt`, `acc`, `pe`, …) |
| `Tools.ShippingMachineLoop.machine_trace_of_loop` (a `Signal.loop`) — the LOOP BRANCH, added by `f3ee9c57` | `Tools.ShippingMachineLoopL.machine_traceL_of_loop` | `DepthLoopChildTest` (generated by the command path), `DepthLoopChildCompareTest` (`isDefEq` the hand-written statement) |
| `Tools.ShippingMachineLoop.machine_trace_of_regs` (bare registers) — added by `f3ee9c57` | `Tools.ShippingMachineLoopL.machine_traceL_of_regs` | NO test at the time of the run ("The `_of_regs` branch is exercised by no test"); `Tests/Compiler/DepthRegsChildTest.lean` of `par/b-28` is WRITTEN for it |
| anything else | refused: `{c}.machine_sound is not built from Tools.ShippingMachineAuto.machine_trace_of_data, _of_loop or _of_regs` | — |

**The parent (and a child WITH calls)** — `endpointParts`
(`Tools/ShippingMachineSeqCommand.lean` 71–91), then the head with the suffix `RA`
(`generateCoreNR`: `headL.appendAfter "RA"`):

| head of `f.machine_sound` | wired twin |
|---|---|
| `Tools.ShippingMachineCausal.machine_trace_of_data_causal` (a `circuit do` with registers and structure-path calls) | `Tools.ShippingMachineCausal.machine_traceL_of_data_causal` |
| `Tools.ShippingMachineCausal.machine_trace_of_comb_calls` (no register, structure-path calls) | `Tools.ShippingMachineCausal.machine_traceL_of_comb_calls` |
| `Tools.ShippingMachineCausal.machine_trace_of_loop_causal` (a `Signal.loop` with calls) | `Tools.ShippingMachineCausal.machine_traceL_of_loop_causal` |
| a transported endpoint (`Eq.mpr`) | read, then REFUSED at depth: `a transported endpoint (not yet at depth)` |
| anything else | refused: `{declName}.machine_sound: no wired twin for its head` |

A child with one-output combinational calls goes through `generateCombNR`
(`composedNn_of_HR` over `c.machine_composedR`); a parent with `instFields = []` is refused
(`one-output combinational calls (the derived boundary needs the general closing)`); a memory call
entry is proved by `memTactic`.

Which of the three parent heads each of the 17 endpoints has was NOT logged by the run. By reading
the declarations (not measured): `engineOnce`, `twinCalls`, `mesh2x2` have no register (the
`_of_comb_calls` head); the other eleven declarations are `circuit do` machines with registers (the
`_of_data_causal` head). No endpoint of the 17 has the `_of_loop_causal` head.

## 4. The 51 targets (17 endpoints × 3 theorems), by full name

The switched command's theorem is the name below; the old loop's was the same name with `NR`
replaced by `NRO` (`…machine_composedNRO1`, …). The fingerprint columns are the pin table of
`Tests/Compiler/DepthSwitchPinTest.lean` (`Expr.hash` of the type, number of leading binders),
recorded BEFORE the switch on poc `25f68ea2`; that file stays and asserts them.

| # | theorem (switched command) | pinned hash | binders |
|---|---|---|---|
| 1 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_composedNR1` | 3806310197 | 12 |
| 2 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_ships_hierNR1` | 2603641402 | 11 |
| 3 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_svNR1` | 775503135 | 11 |
| 4 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_composedNR1` | 1686671341 | 12 |
| 5 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_ships_hierNR1` | 3211064729 | 11 |
| 6 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_svNR1` | 2019951348 | 11 |
| 7 | `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_composedNR1` | 3703413477 | 12 |
| 8 | `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_ships_hierNR1` | 2131524145 | 11 |
| 9 | `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.machine_design_svNR1` | 3188290752 | 11 |
| 10 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1` | 1903175178 | 12 |
| 11 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_ships_hierNR1` | 1466245838 | 11 |
| 12 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_design_svNR1` | 2668439245 | 11 |
| 13 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2` | 3241457573 | 12 |
| 14 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ships_hierNR2` | 1457379173 | 11 |
| 15 | `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_design_svNR2` | 2736187016 | 11 |
| 16 | `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_composedNR1` | 176614720 | 12 |
| 17 | `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_ships_hierNR1` | 2499615973 | 11 |
| 18 | `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_design_svNR1` | 3872311708 | 11 |
| 19 | `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_composedNR1` | 131566955 | 12 |
| 20 | `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_ships_hierNR1` | 4203154352 | 11 |
| 21 | `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR1` | 3539619286 | 11 |
| 22 | `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_composedNR2` | 2454868286 | 12 |
| 23 | `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_ships_hierNR2` | 736515015 | 11 |
| 24 | `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2` | 4088468383 | 11 |
| 25 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_composedNR1` | 1587875193 | 12 |
| 26 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_ships_hierNR1` | 64110983 | 11 |
| 27 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_design_svNR1` | 1628952474 | 11 |
| 28 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_composedNR1` | 3372902074 | 12 |
| 29 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ships_hierNR1` | 2301282515 | 11 |
| 30 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR1` | 861311906 | 11 |
| 31 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_composedNR2` | 131347659 | 12 |
| 32 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ships_hierNR2` | 2543048802 | 11 |
| 33 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2` | 3487859115 | 11 |
| 34 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_composedNR2` | 1001075177 | 12 |
| 35 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ships_hierNR2` | 3032819790 | 11 |
| 36 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR2` | 1388393982 | 11 |
| 37 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_composedNR3` | 3382395632 | 12 |
| 38 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ships_hierNR3` | 191630386 | 11 |
| 39 | `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3` | 4025646973 | 11 |
| 40 | `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_composedNR2` | 378977350 | 12 |
| 41 | `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ships_hierNR2` | 4224889835 | 11 |
| 42 | `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_svNR2` | 1337744565 | 11 |
| 43 | `Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_composedNR1` | 3801280993 | 12 |
| 44 | `Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_ships_hierNR1` | 2697664911 | 11 |
| 45 | `Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_design_svNR1` | 81458612 | 11 |
| 46 | `Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_composedNR1` | 3154440017 | 12 |
| 47 | `Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_ships_hierNR1` | 444608975 | 11 |
| 48 | `Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_design_svNR1` | 3058126545 | 11 |
| 49 | `Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_composedNR1` | 3829026054 | 12 |
| 50 | `Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ships_hierNR1` | 3269999998 | 11 |
| 51 | `Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_design_svNR1` | 408867054 | 11 |

The 17 endpoints `(declaration, depth)`: `parent` 1, `chained` 1, `two` 1, `mid` 1, `grand` 2,
`loopParent` 1, `grandH` 1 and 2, `mid2` 1, `mixD1` 1 and 2, `topD2` 2 and 3, `mixDeep` 2,
`engineOnce` 1, `twinCalls` 1, `mesh2x2` 1. They were generated by the imports
`ShippingCallsCloseDeepTest`, `NoPortsTwoTest`, `NoPortsMidTest`, `NoPortsKidsMid2Test`,
`NoPortsLoopParentTest`, `NoPortsSlotlessEngineOnceTest`, `NoPortsSlotlessTwinCallsTest`,
`NoPortsSlotlessMesh2x2Test` (all in `Tests/AllTests.lean`'s closure).

## 5. The comparison result

What `DepthSwitchTypeTest` did (its own header): on ONE tree, the 17 endpoints were generated again
by the old per-entry loop under the `NRO` names, and per pair of statements — ASSERTED: `isDefEq`
of the two types (after `instantiateMVars`); ASSERTED: standard axioms of both theorems; LOGGED,
not asserted: whether the two types are the same term (`==`). ASSERTED about the run: 17 endpoints,
none twice, exactly 51 comparisons, 51 distinct `NR` and 51 distinct `NRO` names, no theorem
compared with itself, no endpoint skipped.

The log line of the run (quoted from `verification-depth-switch.md`, "Log excerpts"; the prefix is
cut there):

```
an:174:0: DEPTH SWITCH TYPES: 51 of 51 statement pairs isDefEq (the switched command against the per-entry loop of before the switch, both generated on this tree), 17 endpoints, none skipped, standard axioms of all 102 theorems; the same term: 51 of 51 (logged, not asserted). NOT covered: the Keccak sponge (the old loop does not finish on it); children's composed theorems are shared by both loops
```

The secondary check, same run:

```
n:177:0: DEPTH PIN: 51 of 51 FINGERPRINTS EQUAL (Expr.hash of the type, number of leading binders) to the table. A fingerprint is NOT a proof of type equality or of isDefEq (that is DepthSwitchTypeTest); that the table was recorded on edd9496c is the integrator's record, not checked here
```

The integrator's summary (quoted): "PRIMARY — `DepthSwitchTypeTest` (in AllTests): on ONE tree, for
17 endpoints × 3 theorems, the statement generated by the switched command `isDefEq` the one
generated by the old loop: 51 of 51, none skipped, no theorem compared with itself, standard axioms
of all 102 theorems (structurally the same term: 51 of 51, logged only). The children's composed
theorems are shared by both loops: only the parent's loop is old."

In short: **51 of 51 `isDefEq`; the same term 51 of 51 (logged, not asserted); 102 theorems on
standard axioms.**

## 6. What was NOT compared

* **The Keccak sponge** (`keccak256SpongeHW`, depth 1). No old-vs-new comparison exists: "the old
  loop does not finish on it". Its evidence is of another kind — the switched command ends with a
  kernel-checked theorem (run `20261013-151138-switch-sponge-direct`), and the downstream no-ports
  chain builds (run `20261013-150059-switch-sponge`, then through the separate grouped command):

  ```
  lean:73:0: DEPTH SWITCH SPONGE: Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW — machine_composedNR1, machine_ships_hierNR1, machine_design_svNR1 generated by the OLD command #machine_design_svNR (its loop is the grouped one of Tools/ShippingMachineDepthCommandR.lean), kernel-checked, standard axioms. Fingerprints: [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNR1: hash 552262611, 12 binders,
  ```

  (the line is cut in the record; the two other fingerprints are not recorded.)
* **Children's composed theorems.** A child with calls (`mid`, `midH`, `mid2`, …) has ONE composed
  theorem `c.machine_composedNR{n-1}`, generated by the switched generator and used by both loops:
  "only the parent's loop is old". A declaration that is BOTH a child of an endpoint and itself one
  of the 17 at the depth its parent uses (for example `mid` at depth 1 under `grand` at depth 2)
  was compared as a parent; a child's composed theorem that is not one of the 51 was compared with
  nothing.
* **Proof terms.** Statements were compared, not proofs; both sides are kernel-checked and audited
  for axioms by `addTheorem`.
* **Anything outside the 17**: the target-only files that run the command
  (`NoPortsSlotlessSeqFamilyTest`, `RemainingProbeTest`, `KeccakProbeTest`, the sponge probes)
  repeat `mid`, `loopParent`, `twinCalls`, `mesh2x2` and the sponge.
* **The `_of_regs` branch** of `seqChildNProof`: exercised by no test of that run.
* The fingerprints are not evidence of `isDefEq`, and a comparison made in the past is not a
  regression test: after the deletion, what guards the 51 statements is the pin table (§4,
  `DepthSwitchPinTest`, assert mode), which detects a changed TERM, not a changed meaning.

## 7. The separate grouped generator (`#machine_design_svNRG`), removed on `par/b-28`

`Tools/ShippingMachineDepthCommandRG.lean` (round par/a-27; at `77b3ba4f` blob
`93a08c233b3b32718ee556c55c2fd57a25648a63`, at `d71fd052` blob
`61d1a944414f7b7b9d686df226edc4d36ded7152`) was the grouped loop BEFORE it became the loop of
`#machine_design_svNR`; after `bf32874b` it duplicated `generateCoreNR`. Its test,
`Tests/Compiler/DepthGroupedFamilyTest.lean` (blob `b941a27aaeb844e3da2a27ac0b97b4b94c5b6b83` at
`d71fd052`), generated the same 17 endpoints under `…NRG{n}` TWICE — the family facts by the absorb
chain alone, then by the default (`split`, the chain where it fails) — and asserted `isDefEq` with
the `…NR{n}` statements and standard axioms. Its lines in the same run (quoted):

```
.lean:286:0: DEPTH GROUPED FAMILY: 17 of 17 endpoints generated by the grouped loop with statements isDefEq the built ones and standard axioms; FAILED (built theorems present, the grouped ones not generated — see the errors above): []; left out (built theorems absent here): []
```

and, from the earlier run of the same test recorded in `docs/parallel/A-depth-grouped.md` (quoted):

```
.lean:206:0: DEPTH GROUPED: extendBools_absorb, extendBits_absorb — standard axioms
.lean:271:0: DEPTH GROUPED COUNTS Sparkle.Tests.Compiler.MultiInstance.mesh2x2: 8 call entries in 4 groups, as predicted
```

After the switch that test compared the grouped loop with a copy of itself (both sides the same
algorithm), so it is removed with the file it tested. What it covered that NOTHING built covers
now:

* the **absorb-only variant** (`absorb := true`) on the 17 endpoints. In
  `Tools/ShippingMachineDepthCommandR.lean` the absorb chain runs only where the `split` tactic
  fails (`generateCoreNR` passes `absorb := false`); the recorded sponge run used it for the
  bit-vector family (`docs/parallel/A-depth-grouped.md`, "hv (the bit-vector family) [absorb
  chain]"); whether `split` fails on any of the 17 is not recorded here. The two lemmas `Grouped.extendBools_absorb` /
  `Grouped.extendBits_absorb` are kernel-checked when that file is built; their USE is exercised by
  the sponge tests (target-only, heavy) and by no file of `AllTests`;
* the **group count** of `mesh2x2` (8 entries in 4 groups) as an assertion: `generateCoreNR` writes
  the count to the progress file (`… call entries (… of sequential children) in … groups; …`) and
  returns only the theorem's name, so a test cannot read it without a change of that file.

## 8. What remains as regression protection

* `Tests/Compiler/DepthSwitchPinTest.lean` (in `AllTests`, assert mode): the 51 fingerprints of §4.
* The tests that generate the 17 endpoints with the switched command and consume them: the eight
  imports listed in §4 and the check-free generators' family tests behind them (in `AllTests`).
* `DepthLoopChildCompareTest` (in `AllTests`), `DepthLoopChildTest` (target-only): the loop branch.
* `Tests/Compiler/DepthRegsChildTest.lean` (target-only, WRITTEN on `par/b-28`): the `_of_regs`
  branch.
* The sponge: `NoPortsKeccakSpongeTest` (on `par/b-28` it runs the switched command directly) and
  `DepthSwitchSpongeTest`, both target-only and heavy.
* In the generator itself, unchanged and mandatory: every theorem is added by `addTheorem`
  (`addDecl`: the kernel's check; then the axiom test), and a group fact or entry proof containing
  `sorryAx` or a metavariable is an error at once.

## 9. For the integrator: the changes of `par/b-28` (WRITTEN, NOT BUILT)

Removed: `Tools/ShippingMachineDepthCommandRG.lean`, `Tests/Compiler/DepthGroupedFamilyTest.lean`,
`Tests/Compiler/KeccakSpongeGroupedProbe.lean` (commit 2); `Tools/ShippingMachineDepthCommandROld.lean`,
`Tests/Compiler/DepthSwitchTypeTest.lean` (commit 3). Edited: `Tests/Compiler/NoPortsKeccakSpongeTest.lean`
(step 3 runs `#machine_design_svNR … 1`), `Tests/Compiler/DepthSwitchSpongeTest.lean` (header only).
New: `Tests/Compiler/DepthRegsChildTest.lean`, this file. Nothing under `Sparkle/`, no generator file.

Lines the integrator removes (the worker does not edit these two files; numbers as of `d71fd052`):

* `lakefile.lean` 2634–2635: the `lean_lib «Tools.ShippingMachineDepthCommandRG»` and its `roots` line;
* `lakefile.lean` 2642–2643: the `lean_lib «Tools.ShippingMachineDepthCommandROld»` and its `roots`
  line (and one of the blank lines around them);
* `Tests/AllTests.lean` 220: `import Tests.Compiler.DepthSwitchTypeTest`.

Stale text left in files this round may not edit (comments and message strings only, no effect on
elaboration): `Tools/ShippingMachineDepthCommandR.lean` 49–51 (says `…CommandRG.lean` imports it);
`Tests/Compiler/DepthSwitchPinTest.lean` 21, 55, 205, 206 (name `DepthSwitchTypeTest` as the check of
the types — that is now this record, §5).

FIRST BUILD of `par/b-28` (integrator): generator R, `DepthSwitchPinTest` (51 fingerprints),
`DepthLoopChildCompareTest`, `DepthLoopChildTest` and `Tests.AllTests` (1282 jobs) green with RG /
ROld / the type test removed. `DepthRegsChildTest` FAILED at its step 1: the existing child
`childSeq` (`Signal.register 0#8 x`) is taken by the certified GATE route (`readMachine`: "a
combinational gate takes it, not the machine route"), so it has no machine endpoint; the mixed
parent's `machine_sound` was generated. The test now declares its own child `shift3` (three chained
registers: the gate's register root takes at most two); that form is WRITTEN, NOT BUILT. The
`_of_regs` branch therefore remains UNEXERCISED by any built test until that file builds.

Acceptance build order (one job each; stop at the first failure):

1. `lake build Tools.ShippingMachineDepthCommandR` — unchanged file; with the two `lean_lib`s gone it
   confirms the lakefile still loads.
2. `lake build Tests.Compiler.DepthSwitchPinTest` — `DEPTH PIN: 51 of 51 FINGERPRINTS EQUAL`.
3. `lake build Tests.Compiler.DepthLoopChildCompareTest Tests.Compiler.DepthLoopChildTest`.
4. `lake build Tests.Compiler.DepthRegsChildTest` — NEW: `DEPTH REGS CHILD: … GENERATED …` (steps 0–5
   assert) and `DEPTH REGS CHILD CHECK-FREE …` (which optional theorems exist).
5. `lake build Tests.AllTests` (after the list edits above).
6. HEAVY, target-only: `lake build Tests.Compiler.NoPortsKeccakSpongeTest` (edited: the first build of
   the switched command in THIS file's closure; `-t 3600`, 3 GiB), optionally
   `Tests.Compiler.DepthSwitchSpongeTest` before it (the short form; its commands are unchanged).

## 10. Integration record (integrator, 2026-10-13)

Verified tree `557906b4c913f70881879f2e0554218fa6904770` = poc d71fd052 + par/b-28 (d9e9e638 record, dacffd9b RG removal, 79a1ff4d old-loop removal,
fcafa158 the rewritten `DepthRegsChildTest`; worker files unchanged) + `lakefile.lean` (the two `lean_lib`
entries of RG / ROld removed) + `Tests/AllTests.lean` (`DepthSwitchTypeTest` import removed,
`DepthRegsChildTest` added). cgrun 3 GiB, swap 0.

| run | command | result |
|---|---|---|
| `20261013-162133-b28-tests` | `lake build Tools.ShippingMachineDepthCommandR Tests.Compiler.DepthSwitchPinTest Tests.Compiler.DepthLoopChildCompareTest Tests.Compiler.DepthLoopChild` | result=exit-code, memory_peak_file=995127296,  |
| `20261013-162214-b28-sponge` | `lake build Tests.Compiler.NoPortsKeccakSpongeTest ` | result=success, memory_peak_file=1616068608, Build completed successfully (583 jobs). |
| `20261013-163547-b28-regs` | `lake build Tests.Compiler.DepthRegsChildTest ` | result=success, memory_peak_file=373981184, Build completed successfully (563 jobs). |
| `20261013-163602-b28-final` | `lake build Tests.AllTests Tests.Compiler.DepthLoopChildTest Tests.Compiler.DepthSwitchSpongeTest ` | result=success, memory_peak_file=1632382976, Build completed successfully (1285 jobs). |

(`b28-tests` exit 1 was the FIRST version of `DepthRegsChildTest` only — its child `childSeq` is taken by the
gate route; every other target of that run, AllTests included, built. `b28-regs` / `b28-final` are the
rewritten test and the committed tree.)

After the removal: `DepthSwitchPinTest` 51 fingerprints (assert mode) green; `NoPortsKeccakSpongeTest` and
`DepthSwitchSpongeTest` build with the switched `#machine_design_svNR` directly; the generator's kernel
check and axiom audits unchanged.

`_of_regs` branch, now exercised: `shift3` (three chained registers; `machine_sound` built from
`machine_trace_of_regs`) as a child of the register-free parent `regsParent` (also calling `cnt`):
`shift3.seq_child_runN` GENERATED by `generateSeqChildN` inside `#machine_design_svNR regsParent 1`
(absent before the command), `seqChildRunN_full` at `machine_traceL_of_regs`, standard axioms. The
optional part (`#machine_closes_at`, `#machine_no_ports_seq` on `regsParent`) logged OK; it is log-only and
nothing is claimed from it. Reaching this branch from a parent WITH registers is refused upstream
(`causalFactE`), by reading.

No longer exercised by any test: the absorb-only variant on the 17 endpoints, and the `mesh2x2`
"8 entries in 4 groups" assertion (recorded in §7).
