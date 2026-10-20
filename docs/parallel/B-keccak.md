# B-keccak — the Keccak declarations and a log-only probe (round par/b-18)

STATE: **WRITTEN, NOT BUILT, NOT RUN.** Nothing below is measured in this
round. [R] = read in the source at the line given; [D] = said by a document
of the repository (cited), not re-checked; [P] = PREDICTION.

Base: `50daf208` (`poc/roundtrip-proof`), branch `par/b-18`.
Files of this round: `Tests/Compiler/KeccakProbeTest.lean` (the probe),
this note. No existing file is changed; no `Tools/` file was needed.

## 1. The declarations [R]

`IP/Crypto/Keccak256HW.lean`, `namespace Sparkle.IP.Crypto.Keccak256HW` (30);
`IP/Crypto/Keccak256Sponge.lean`, `namespace Sparkle.IP.Crypto.Keccak256Sponge` (51).

| declaration | where | `@[hardware_module]` | value | inputs | state | result | calls |
|---|---|---|---|---|---|---|---|
| `keccakRcHW` | `Keccak256HW` 42–60 | yes | `kLut! round [32 × Signal.pure _#64]` (24 round constants + 8 zeros) | `{dom}`, `round : BitVec 5` | none | ONE `Signal dom (BitVec 64)` | none |
| `keccakF1600HW` | `Keccak256HW` 168–339 (`circuit do` at 174) | **no** (a plain `def`) | `circuit do` | `{dom}`, `start : Bool`, `in0…in24 : BitVec 64` (27 binders) | 27 registers: `l0…l24 : BitVec 64` (175–187), `cntR : BitVec 5` (188), `doneR : Bool` (189) = 1606 bits | structure `KeccakFOut` (85–120): **27** fields `l0…l24 : BitVec 64`, `round : BitVec 5`, `done : Bool` | ONE call: `keccakRcHW (cntSig - 1#5)` (252), result used in `nl0` (253) |
| `wKeccakF` | `Keccak256Sponge` 82–91 | yes | NOT a `circuit do`: the application `keccakF1600HW start in0 … in24` (a wrapper) | as `keccakF1600HW` | (its core's) | `KeccakFOut dom` | (its core's) |
| `keccak256SpongeHW` | `Keccak256Sponge` 94–257 (`circuit do` at 102) | **no** (the entry) | `circuit do` | `{dom}`, `start : Bool`, `nBlocks : BitVec 2`, `m0…m33 : BitVec 64` (37 binders) | 30 registers: `s0…s24 : BitVec 64` (104–116), `blkR`, `nBlkR : BitVec 2` (119–120), `doneR`, `kfDonePrev`, `kfDoneP2 : Bool` (121–127) = 1607 bits | structure `SpongeOut` (67–74): 5 fields `d0…d3 : BitVec 64`, `done : Bool` | ONE call `wKeccakF kfStart <25 lane expressions>` (197–202): 26 arguments; its fields read: `kf.l0 … kf.l24` (210–234) and `kf.done` (241) — 26 of the 27; **`kf.round` is never read** |

Call structure: `keccak256SpongeHW → wKeccakF (= keccakF1600HW) → keccakRcHW`.
There is no separate round-function declaration: the round (θ ρ π χ ι) is
inlined in `keccakF1600HW` (217–277, 60 `let`s of 64-bit operators);
`rotL64Sig` (64) is `@[reducible, inline]` and not used by the FSM;
`Lanes25` (130) is not used by these three.

Correction of `A-census-2.md` §2.3 ("26 output fields"): `KeccakFOut` has 27
fields; 26 is the number of fields the sponge READS (so, by reading, 26 call
entries of one instance with `instFields` of length 26 — to be confirmed by
the probe's steps 3–4).

### Shape classes [R for the source, P for what the reader returns]

| declaration | route [D] | shape, in the built generators' terms |
|---|---|---|
| `keccakRcHW` | GATE route: certified by the applicative arm (`docs/ShippingCompiler-Coverage.md` 224–229); `readMachine` without `allowGate` refuses such a declaration (`Tools/ShippingMachineCommand.lean` 426–428) | one-output combinational gate child, 1 input of 5 bits, output 64 bits — `rcH`'s class (`ShippingMachineDepthHTest` 19) with a 32-entry table instead of one mux |
| `wKeccakF` | MACHINE route, "read through its core" since the unfolding budget is 16M (`RtlStructureTest` 752–755; `docs/CertifiedRoundtrip-TODO.md` 1416) | register machine (27 slots) with ONE one-output call of ONE gate child: `instFields = []` [P], the ONE-OUTPUT closing — `midH`'s class (`ShippingMachineDepthHTest` 25). New against `midH`: a wrapper entry; 27 outputs; 26 declared hardware binders; 1606 state bits |
| `keccak256SpongeHW` | MACHINE route with ONE clocked instance of `wKeccakF` connected port by port (`closeInstsG`; `RtlStructureTest` 718–726, pins: 57 registers, 1 `wKeccakF` instance, 1 `keccakRcHW` instance, 728–761) | domain-polymorphic register parent (30 slots) under the GENERAL closing (`instFields ≠ []` [P]) whose one callee is a register machine with a one-output gate call, depth 1 — `mid2`'s class (`ShippingDesignSVTest` 24–32; BUILT as an entry by `NoPortsKidsMid2Test`, commit `b19ad828`). New against `mid2`: 26 call entries of one instance instead of 2; 26 argument `let`s; an UNREAD child output (`round`); 37 declared binders; a callee that is a wrapper |

## 2. How they are compiled / measured today [D] (nothing run here)

* `keccakRcHW`: certified gate (above); its `#gate_child` data are generated
  by the corpus measurement ("all 5 gate children of the corpus … `keccakRcHW`
  … `|GATECHILD|`", `docs/CertifiedRoundtrip-TODO.md` 1359–1361).
* `wKeccakF`: linked theorem measured ("27/27 callers … `wKeccakF`", TODO
  1346–1347), composed ("`#machine_composed f` … `wKeccakF`", TODO 1368–1370),
  shipped module with every module premise evaluated true ("26 of 26 … the
  crypto wrappers (`wKeccakF`, …)", `docs/ShippingCompiler-TrustBase.md`
  1436–1442; first rejected by the emitted-Verilog check, fixed by
  `SF4.bitwiseShlW`, 1454–1458). These are the OLD endpoints (check premises
  evaluated, boundary traced), in a sweep at an earlier revision.
* The sponge: **UNMEASURED.** "Real Keccak sponge: not completed. Generation
  inside the measurement exceeded the 1500 s per-file limit; an unbounded run
  was stopped for memory" (TrustBase 1401–1403, 1721–1723; the limit:
  `scripts/shipping-coverage/endpoints.sh` 37). The files of that sweep are
  `Tests/IP/Crypto/Keccak256Sponge{,JIT}Test.lean`, whose declarations are
  the projections `synth_spongeD0` / `synth_spongeDone`
  (`Keccak256SpongeTest.lean` 136–165), and the tail runs the whole old chain
  on every declaration — WHICH generator did not end is not recorded.
* No `#machine_*` / `#gate_*` command is run on any of the three in any file
  of the repository (`A-census-2.md` §2.3, re-checked by `grep` over
  `Tests/`, `Tools/`, `IP/`).
* The corpus sweep runs no check-free generator at all (`A-census-2.md` §2.3,
  second row).

## 3. Which built generator applies by shape

| generator | `keccakRcHW` | `wKeccakF` | `keccak256SpongeHW` |
|---|---|---|---|
| `#gate_child` | YES (its class) | no (machine route) | no |
| `#machine_endpoint` | no (gate route; `generateSourceDefs` only) | YES | YES (recurses into `wKeccakF`'s endpoint when missing, `generateCore` 2450–2454) |
| `#machine_linked` / `#machine_composed` | — | YES (`midH`: `ShippingMachineDepthHTest` 46, 48) | no: sequential child — the depth commands |
| `#machine_closes_at` | — | YES (`midH`: `ShippingCallsCloseTest` 78) | via `#machine_closes_deep` (`grandH`, `topD2`: `ShippingCallsCloseDeepTest` 29, 33) |
| `#machine_design_svHR` | — | YES (`midH`: `ShippingChildBoundaryTest` 349) | no (`composedR`: combinational children only) |
| `#machine_oneout` | — | YES by scope (`Tools/ShippingOneOutGenCommand.lean` 167–190: register, `instFields = []`, gate callee with `#gate_child` data) — `midH`: `OneOutMidHTest` | refused [P]: `instFields ≠ []` |
| `#machine_design_svNR f 1` | — | — | YES (`mid2`: `NoPortsKidsMid2Test`) |
| `#machine_no_ports f 1` | — | — | refused [P]: the callee has calls of its own (`RemainingProbeTest` table B, `grandH`) |
| `#machine_no_ports_kids f 1` | — | — | YES by `scopeK` (`Tools/ShippingNoPortsKidsCommand.lean` 76–127): register, general closing, one callee = register machine, one-output closing, ONE gate grandchild, depth 1 |
| `#machine_boundary_close` | — | — | YES on the `_closed` form (`mid2`, `grandH`) |
| leaf-as-entry design head | NONE exists for a gate-route entry (`A-census-2.md` (b3)) | — | — |

### What in the shape may be outside every BUILT scope (all unknown before the probe)

1. **Size of the kernel checks.** The endpoint's checks (`machine_ok`,
   `machine_body`, the source `rfl`s) on a transition with 27 / 30 slots of
   64 bits and ≈ 100 `let`s of 64-bit operators; the round's shifts by
   literals (`<<< 44#64`); the 32-entry table as a term. The handoff's known
   pitfall is a kernel comparison falling into unary evaluation of a wide
   value (`docs/ShippingCompiler-ClaudeCode-Handoff.md` 385–392). Built
   endpoints of wide machines exist (`EcdsaSignDemo.wMulN`, `P256SignDemo.wMul`:
   `ShippingMachineCommandTest` 59–63), not of 1600 state bits.
2. **Per-declaration `by decide` data conditions** of `#machine_oneout`
   (`wKeccakF.oneout_outChars`, `_outScalar`, `_outTy` over 27 outputs;
   `callArgsOk`) and of `#machine_no_ports_kids` (`machine_kidsK1`,
   `_runFactsK1`, `_outsGK1`, `_maskedGK1`, `_designPK1` over 26 call entries
   × 26 argument `let`s, 63 input binders). Built at 2 entries / 1 argument.
3. **An unread child output** (`kf.round`): every built general-closing
   parent reads every field of its child (`mid2`, `grandH`, `mixD1`:
   `CntOut.n`, `.hit`). Whether `portsMatch` / `outsCheck` / `KidFacts` are
   stated for the ports READ or for all of the child's ports was NOT read to
   the end here.
4. **A wrapper as the callee and as the one-output parent**: `wKeccakF`'s
   value is an application; `MachineDefines wKeccakF` is about the entry as
   read (unfolded). Built wrapper ENDPOINTS exist (item 1); a wrapper under
   `#machine_design_svHR` / `#machine_oneout` / as a `OneOutKid` does not.
5. **Not in question**: a multi-output GATE child (there is none — the
   multi-output child is the sequential `wKeccakF`); a memory; a
   `Signal.loop`; several different callees.

## 4. The probe: `Tests/Compiler/KeccakProbeTest.lean`

Target: `lake build Tests.Compiler.KeccakProbeTest` (target-only, never
imported, not for `Tests/AllTests.lean`). Imports: `IP.Crypto.Keccak256Sponge`
and eleven `Tools.*Command*` / generator modules — no `Tests.*` import.
Run with `SPARKLE_MACHINE_PROGRESS=<abs file>` (on `cgrun.sh`'s allow-list,
line 72): every probe line and the generators' own `progress` lines are
appended there at once with a ms clock and VmRSS / VmHWM. After a timeout
the progress file is the result; the build's message log shows nothing of a
killed command.

Wrapper `#keccak_probe "n" "what" needs [constants] in cmd`: SKIPPED when a
named constant is missing; else `KECCAK PROBE START n what`, the command
inside `try`, then `OK (ms)` or `FAILED (ms) — message` with the environment
and message log put back (the pattern of `RemainingProbeTest`'s
`#probe_log`, plus the guard, the clock and the file). `#keccak_read`: the
reader (`readMachine`; where it refuses, again with `allowGate`).
`#keccak_premises [thm, …]`: the proposition binders and the antecedents
under the existentials, `ALLOWED` / `NOT ALLOWED` by
`Tools.ShippingFinalGoalCommand.allowed` / `analyse`; adds no constant.

### Steps and PREDICTIONS [P] (none is a result)

| step | what | prediction | basis |
|---|---|---|---|
| 0a / 0b | wrapper self-test | FAILED / OK | by construction; anything else = a defect of the probe file |
| 1 | read `keccakRcHW` | FAILED "a combinational gate takes it"; `(allowGate)` OK: nDecl 2, slots 0, no call, 1 output | `readMachine` 426–428; `rcH` |
| 2 | read `keccakF1600HW` | OK: nDecl 27, 27 slots (25 × 64, 5, 1), 1 call entry of `keccakRcHW` (result `bits 64`), `instFields = []`, 27 outputs | source |
| 3 | read `wKeccakF` | OK with the same data as step 2 | "read through its core" |
| 4 | read the sponge | OK: nDecl 37, 30 slots, 26 call entries of `wKeccakF` in ONE (callee, argument lets) group of 26 lets, `instFields` = `l0…l24`, `done` (26), 5 outputs | source; the pins of `RtlStructureTest` |
| 5 | `#gate_child keccakRcHW` | GO | generated by the corpus measurement [D]; cost of the 32-entry `rfl` unknown |
| 6 | `#machine_endpoint wKeccakF` | GO, cost UNKNOWN (the first expensive step) | a linked theorem of it was measured [D], which needs the endpoint |
| 7 | `#machine_linked wKeccakF` | GO | measured [D] |
| 8 | `#machine_composed wKeccakF` | GO | measured [D] |
| 9 | `#machine_endpoint` sponge | UNKNOWN (go / timeout / memory) | the only record is the unfinished sweep; `mid2`-class by shape |
| 10 | `#machine_closes_at wKeccakF` | UNKNOWN; if it refuses, in a decided data condition | `midH` built; never run on 27 outputs |
| 11 | `#machine_design_svHR wKeccakF` | GO if 6 is affordable | the old `machine_ships_hierH` was generated [D]; the R head never |
| 12 | `#machine_oneout wKeccakF` | UNKNOWN; a refusal would be `ONEOUT GEN … FAILED (data condition … [name])` | scope fits by reading; item 2 |
| 13 | `#machine_design_svNR` sponge 1 | UNKNOWN; the most likely place of a timeout after 9 | never run on a wide parent |
| 14 | `#machine_closes_deep` sponge | UNKNOWN | `topD2` / `grandH` built |
| 15 | `#machine_no_ports_kids` sponge 1 | UNKNOWN; refusal lines of `scopeK` are named; item 3 could fail a decided condition | `mid2` built |
| 16 | `#machine_boundary_close` | GO if 15 | `mid2`, `grandH` |

Guards (a decision of this file, one line each to relax): step 9 needs
`wKeccakF.machine_sound` (so the sponge's endpoint does not regenerate a
child endpoint that just failed); steps 13–14 need `wKeccakF.machine_closes_at`
(so `preClose` does not rerun a closing that just failed) — if step 10
FAILS quickly, rerun 13 with that guard removed: the depth endpoint then
keeps the child's closing as a premise.

NOT in the probe: the OLD depth chain (`#machine_composedN`,
`#machine_ships_hierN`, `#machine_design_svN`: check premises, superseded by
the R heads); `#sim` / any compile of the design; any audit (`stdAxioms`,
checker-constant inventory) — the generators check standard axioms
themselves where they do; nothing is asserted.

### What a result would mean

| outcome | next unit |
|---|---|
| 0a/0b wrong, or the build fails before `0b: OK` | fix the probe file (not a Keccak result) |
| 1–4 differ from the predictions | correct §1 / §3 of this note first; the chain below is chosen from the reader's data, not from the reading |
| 5–8 OK, 9 OK, 10–16 OK | Keccak is category (a) of `A-census-2.md` §4: write the proper test `KeccakEntryTest` (the chain of `NoPortsKidsMid2Test` on the sponge + `OneOutMidHTest` on `wKeccakF`, with audits and assertions) with the measured times as its budget; decide whether it can be in `AllTests` at that cost |
| 6 or 9 does not end in the limit | a COST unit, not a proof unit: bisect with the generators' `progress` lines (which kernel check), then a small `circuit do` at the real widths (handoff 392); candidates: lanes reduced to k registers of 64 bits, the round alone |
| 6 FAILED with a message | the endpoint generator on this shape (wrapper + 27-field result): a reader / generator unit on `wKeccakF` alone |
| 10 or 12 FAILED in a named data condition | that condition on 27 outputs / a 5-bit argument: a per-declaration data lemma, or the generator's statement of it (`oneout_*`) |
| 13 OK, 15 REFUSED by `scopeK` | the refusal line names the missing prerequisite or the shape clause |
| 15 FAILED in `machine_kidsK1` / `_runFactsK1` / `_outsGK1` / `_designPK1` | item 3 (unread output) or item 2 (size): read which, then either a general lemma (`Tools/ShippingKeccak*.lean` only if it is general: "a child port no call entry reads") or a cost unit |
| any step killed for memory (the progress file's VmHWM near the cap) | the same cost unit; the step and the last `progress` line say where |

## 5. Suggested limits

`cgrun.sh -n keccak-probe -m 3G -s 0 -t 3600 -- lake build Tests.Compiler.KeccakProbeTest`
with `SPARKLE_MACHINE_PROGRESS` set. 3600 s: the old sweep's 1500 s per file
was not enough for the sponge's projections, and this file runs two
declarations' chains in one process. A first run at 1800 s is also
informative (steps 1–8 are expected well inside it [P]); the progress file
is appended, so use a fresh file per run.

## Run record (integrator, 2026-10-13) — the probe RUN; it claims nothing

`20261013-080244-keccak-probe`: `lake build Tests.Compiler.KeccakProbeTest` on poc 7ae29e5c + this probe, cgrun 3 GiB, swap 0,
limit 3600 s. Result: TIMEOUT at step 13 (result=timeout, memory_peak_file=3143958528,
events: low 0 high 64280 max 0 oom 0 oom_kill 0 oom_group_kill 0 ) — the cgroup reached memory.high (reclaim throttling, no OOM kill).

- Steps 0–12 OK, each 5–50 s, RSS peak about 2.3 GB: reader data of all four declarations; `#gate_child
  keccakRcHW`; `#machine_endpoint` / `#machine_linked` / `#machine_composed` on `wKeccakF`;
  `#machine_endpoint` on `keccak256SpongeHW` (49.7 s); `#machine_closes_at`, `#machine_design_svHR`,
  `#machine_oneout` on `wKeccakF` — the probe generated `wKeccakF.machine_design_svH_full(_closed)`
  (4 premise lines each). Nothing is kept: a proper test for `wKeccakF` is the next same-pattern step.
- Step 13, `#machine_design_svNR keccak256SpongeHW 1`: started and never returned within the limit; steps
  14–16 not reached. Not established: whether it is slow or diverging, and which sub-step of the depth
  generator it was in (the generator's own progress lines stop at the START line).

```
195144690 KECCAK PROBE START 0a self-test of the wrapper (FAILED is the expected line: an unknown constant) [VmRSS:	 1831960 kB] [VmHWM:	 1832844 kB]
195144691 KECCAK PROBE 0a self-test of the wrapper (FAILED is the expected line: an unknown constant): FAILED (1 ms) — Unknown identifier `keccakProbeNoSuchConstant` [VmRSS:	 1832284 kB] [VmHWM:	 1832
195144691 KECCAK PROBE START 0b self-test of the wrapper (OK is the expected line) [VmRSS:	 1832284 kB] [VmHWM:	 1832844 kB]
195144692 KECCAK PROBE 0b self-test of the wrapper (OK is the expected line): OK (0 ms) [VmRSS:	 1832408 kB] [VmHWM:	 1832844 kB]
195144692 KECCAK PROBE START 1 read Sparkle.IP.Crypto.Keccak256HW.keccakRcHW [VmRSS:	 1832428 kB] [VmHWM:	 1832844 kB]
195144714 KECCAK PROBE 1 read Sparkle.IP.Crypto.Keccak256HW.keccakRcHW: FAILED (22 ms) — the machine reader refuses it: Sparkle.IP.Crypto.Keccak256HW.keccakRcHW: a combinational gate takes it, not the
195144714 KECCAK PROBE START 1 read Sparkle.IP.Crypto.Keccak256HW.keccakRcHW (allowGate) [VmRSS:	 1834480 kB] [VmHWM:	 1834480 kB]
195144744 KECCAK PROBE 1 read Sparkle.IP.Crypto.Keccak256HW.keccakRcHW (allowGate): OK (29 ms) — read as a gate-route child's source function. nDecl=2; declared binders [domain, bits 5]; binders=2; sl
195144745 KECCAK PROBE START 2 read Sparkle.IP.Crypto.Keccak256HW.keccakF1600HW [VmRSS:	 1840112 kB] [VmHWM:	 1840112 kB]
195154859 KECCAK PROBE 2 read Sparkle.IP.Crypto.Keccak256HW.keccakF1600HW: OK (10092 ms) — the MACHINE route reads it. nDecl=27; declared binders [domain, bool, bits 64, bits 64, bits 64, bits 64, bit
195154859 KECCAK PROBE START 3 read Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF [VmRSS:	 1943560 kB] [VmHWM:	 1945372 kB]
195165096 KECCAK PROBE 3 read Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF: OK (10216 ms) — the MACHINE route reads it. nDecl=27; declared binders [domain, bool, bits 64, bits 64, bits 64, bits 64, bits
195165096 KECCAK PROBE START 4 read Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW [VmRSS:	 1944504 kB] [VmHWM:	 1963464 kB]
195170496 KECCAK PROBE 4 read Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW: OK (5387 ms) — the MACHINE route reads it. nDecl=37; declared binders [domain, bool, bits 2, bits 64, bits 64, bits 6
195170497 KECCAK PROBE START 5 keccakRcHW #gate_child [VmRSS:	 1899208 kB] [VmHWM:	 1963464 kB]
195175812 KECCAK PROBE 5 keccakRcHW #gate_child: OK (5314 ms) [VmRSS:	 1883600 kB] [VmHWM:	 1963464 kB]
195175815 KECCAK PROBE START 6 wKeccakF #machine_endpoint [VmRSS:	 1883756 kB] [VmHWM:	 1963464 kB]
195198780 KECCAK PROBE 6 wKeccakF #machine_endpoint: OK (22965 ms) [VmRSS:	 2281604 kB] [VmHWM:	 2315768 kB]
195198785 KECCAK PROBE START 7 wKeccakF #machine_linked [VmRSS:	 2259856 kB] [VmHWM:	 2315768 kB]
195212579 KECCAK PROBE 7 wKeccakF #machine_linked: OK (13794 ms) [VmRSS:	 2273868 kB] [VmHWM:	 2315768 kB]
195212583 KECCAK PROBE START 8 wKeccakF #machine_composed [VmRSS:	 2273868 kB] [VmHWM:	 2315768 kB]
195226077 KECCAK PROBE 8 wKeccakF #machine_composed: OK (13494 ms) [VmRSS:	 2262356 kB] [VmHWM:	 2315768 kB]
195226081 KECCAK PROBE START 9 keccak256SpongeHW #machine_endpoint [VmRSS:	 2261588 kB] [VmHWM:	 2315768 kB]
195275805 KECCAK PROBE 9 keccak256SpongeHW #machine_endpoint: OK (49723 ms) [VmRSS:	 2211804 kB] [VmHWM:	 2320000 kB]
195275808 KECCAK PROBE START 10 wKeccakF #machine_closes_at [VmRSS:	 2211804 kB] [VmHWM:	 2320000 kB]
195288649 KECCAK PROBE 10 wKeccakF #machine_closes_at: OK (12840 ms) [VmRSS:	 2197604 kB] [VmHWM:	 2320000 kB]
195288651 KECCAK PROBE START 11 wKeccakF #machine_design_svHR [VmRSS:	 2195124 kB] [VmHWM:	 2320000 kB]
195321771 KECCAK PROBE 11 wKeccakF #machine_design_svHR: OK (33120 ms) [VmRSS:	 2194776 kB] [VmHWM:	 2320000 kB]
195321780 KECCAK PROBE START 12 wKeccakF #machine_oneout [VmRSS:	 2183904 kB] [VmHWM:	 2320000 kB]
195341666 KECCAK PROBE 12 wKeccakF #machine_oneout: OK (19885 ms) [VmRSS:	 2189268 kB] [VmHWM:	 2320000 kB]
195341676 KECCAK PROBE START 13 keccak256SpongeHW #machine_design_svNR 1 [VmRSS:	 2189728 kB] [VmHWM:	 2320000 kB]
```
