# G8 class-coverage census: result

Issue `sparkle-gaps-g8-measure`.
- **Plan:** scripts/gaps/G8_CENSUS_FREEZE.md, approved at c3e979f1, with Amendments 2 (0df300dc) and 3 (6533e3d9).
- **Base:** poc eb5099fa.
- **Tool:** `Tools/ShippingSharedLeafCensus.lean` is unchanged since cbae5d3a. Later commits only add chunk files, lakefile
  entries and docs.
- **Source tree:** no compiler, production or existing-test change.
- **In poc (sparkle-gaps-g8-int):** only the tool, the control test, their two `lean_lib` entries and these docs are
  merged. The 66 chunk files `Tests/Gaps/G8Census*.lean` and their lakefile entries stay on branch `par/g8-measure`
  (0cf85531) and are not in poc. Every chunk job below names the commit that carries its file.

## Headline
**The census covers U-measured:** 12134 constants, from 453 of the 459 frozen corpus modules.
- It counts every constant whose defining module is one of those 453 modules, with no name filter.

**T0-eligible: 20 constants.** All 20 are test declarations in `Tests.Compiler.*` / `Sparkle.Tests.Compiler.*`.
- **Within the 453 measured modules, none of them is in IP/, Examples/, or any test directory other than Tests/Compiler.**
  Nothing is concluded about the 6 unmeasured modules (below), among them `Tests.IP.Net.TCPHeaderTest` (module 429), whose
  census OOMed even alone.
- T0-eligible means candidate only: `group`, the GEN-SHAPE fields and the full-data checks are not evaluated.
- The breakdown:
  - 7 pass strictly: 6 M:PASS and 6 Q:PASS, 5 of them both. The names are listed below.
  - 13 pass only as Q:PASS-noleafcall, with no M:PASS (Amendment 2: candidate-only).

**Scope of the next three points:** they cover only the PARENT rows observed in the 453 measured modules. They say nothing
about module 429 (`Tests.IP.Net.TCPHeaderTest`, unmeasured: census OOM alone) or the other 5 unmeasured modules.

**Every IP design that reads as a PARENT in a measured module fails T0:**
- 12 fail with FAIL:P3 (the top has memory or memory-named call entries):
  - 11 in `Sparkle.IP.Video.H264` (the encoder/decoder pipelines, CAVLC, DCT/IDCT, quant/dequant, reconstruct);
  - `Sparkle.IP.RV32.rv32iCore`.
- `Sparkle.IP.YOLOv8.ActivationBuffer.activationDoubleBuffer` fails with FAIL:P1.
- The other non-Tests.Compiler PARENT rows observed in measured modules fail on P1, P2, P3 or P4: the RoundTrip IVerilogSim tops, the Keccak sponge sim top,
  `synth_loop_bram`, `memCirc` and the `caller*` examples.

**The bound (freeze Amendment 1, relative to the MachineDefines shape tie):**

  #tops of C4/C5 members among the constants of the 459 modules
    ≤ T0-eligible (20) + UNEVALUATED-KIND (5652) + READ-TIMEOUT (0) + constants of the unmeasured modules (unknown)

- Six modules are unmeasured. Their constant counts are unknown, because their census never ran to completion. So the
  numeric bound is **incomplete in that term** (Amendment 3).
- The UNEVALUATED-KIND term is 5197 theorems, 117 axioms, 109 constructors, 104 inductives, 104 recursors and 21 opaques.
  These are counted as unknown, never as non-members.
- The 3 non-lake files (G8_NOLIB_MODULES.txt) are outside U and outside this bound.

## Totals over U-measured (12134 constants)
| row class | count |
|---|---|
| READ-FAIL (readMachine refuses) | 5973 |
| UNEVALUATED-KIND | 5652 |
| LEAF (no call entry) | 367 |
| PARENT (T0 evaluated) | 142 |
| READ-TIMEOUT | 0 |

The 142 PARENT rows, by first failing condition (UNKNOWN callee reads: 0):

| verdict | M | Q |
|---|---|---|
| FAIL:P1 (no slots) | 8 | 8 |
| FAIL:P2 (no insts / instFields) | 51 | 51 |
| FAIL:P3 (memory or memory-named entry in the top) | 33 | 33 |
| FAIL:P4 (entries not paired) | 22 | 22 |
| FAIL:R1 (a wrapper does not read) | 2 | 2 |
| FAIL:M1 / M2 / M3 | 17 / 1 / 2 | — |
| FAIL:Q1 / Q2 | — | 3 / 4 |
| PASS | 6 | 6 |
| PASS-noleafcall | — | 13 |

**Split by declaration-name prefix:** this is not a per-module attribution. A row records the declaration, not its module.

| prefix | PARENT | LEAF | READ-FAIL | UNEVALUATED-KIND |
|---|---|---|---|---|
| contains `Tests.Compiler` | 90 | 95 | 3838 | 4635 |
| other | 52 | 272 | 2135 | 1017 |

**Secondary breakdown (name categories; the bound does not use it):**
- All of U: plain 6811, generated-mark 2418, internal 2027, `match_` 406, `eq_` 234, `inst` 133, `sizeOf` 105.
- The plain subset: READ-FAIL 3797, UNEVALUATED-KIND 2649, LEAF 251, PARENT 114. All 20 T0-eligible rows are plain.

## T0-eligible constants (candidates only)
- **M:PASS and Q:PASS:**
  - `Tests.Compiler.KaryThreeTest.topshare3`;
  - `Tests.Compiler.SharedLeafGenTest.{topinter, topshare2, topthree}`;
  - `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand`.
- **M:PASS only:** `Tests.Compiler.SharedLeafGenTest.topmemleaf` (Q:FAIL:Q2).
- **Q:PASS only:** `Tests.Compiler.SharedLeafGenTest.topmemcallee` (M:FAIL:M1).
- **Q:PASS-noleafcall only (13):**
  - `Tests.Compiler.CallWidthHuntTest.pClkIn`;
  - `Tests.Compiler.KaryThreeTest.{wrapA, wrapB, wrapC}`;
  - `Sparkle.Tests.Compiler.RtlStructureTest.outerShared`;
  - `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two`;
  - `Tests.Compiler.SharedLeafGenTest.{wrapG2, wrapP, wrapQ, wrapR}`;
  - `Sparkle.Tests.Compiler.ShippingMachineSeqTest.{chained, mid, parent}`.

**About the known members:** the class members `P_M`/`P_Q` (topshareM/topshareQ, Tests/Compiler/SharedLeafMemKidTest.lean)
are not in the corpus, by the run.sh:25 file set. They are covered by the controls instead (below). Several eligible tops
(`SharedLeafGenTest.*`, `KaryThreeTest.topshare3`) are siblings written for the shared-leaf generators.

## Unmeasured modules (inside U, outside U-measured)
| # | module | reason (single-module job) |
|---|---|---|
| 283 | Tests.Compiler.SingleOutStaleProbe | fails to build alone. `g8-c07aaaab-41418c7d`, exit 1: 107:0 "SINGLEOUT: the two modules are EQUAL". This is the baseline non-pass already classified at 0054b6b2 in the C45 manifest |
| 429 | Tests.IP.Net.TCPHeaderTest | census OOM at 12Gi even alone. `g8-c10babba-3cad56ae`, exit 137, OOMKilled. UNMEASURED/unknown, never non-member |
| 453 | Tests.Verification.ConeSharingPremises | fails to build alone. `g8-c11baab-c5cab928`: 23:0 "expected 26 shared wires, got 73" |
| 454 | Tests.Verification.DeepElabReifyDemo | fails to build alone. `g8-c11baba-f19e88fc`: 62:0 "Cannot synthesise Sparkle.Core.runCircuitH"; 275:0 "closers exhausted" |
| 457 | Tests.Verification.VerifyElabDemo | fails to build alone. `g8-c11bbab-9983cf65`: 42:0 omega |
| 458 | Tests.VerifyVerilog | fails to build alone. `g8-c11bbba-4bb630e4`: 44:38 "Unknown identifier current" |

- **Five of these fail independently of the census:** the module itself does not elaborate. Whether they also fail at
  base eb5099fa was not built here, except module 283, which is known from the C45 record. They are therefore not
  classified as baseline non-passes in this unit.
- **Module 429:** the census process OOMed on that module alone.

## Controls (Amendment 2 evidence)
`g8-ctl-0df300dc`: exit 0, 921 lake jobs, head=base=0df300dc, log `088e039f4c0fbd73`. It was built in a separate detached
worktree. All the assertions of `Tests/Compiler/SharedLeafCensusControlTest.lean` held:

| control | M | Q |
|---|---|---|
| topshareM | PASS | FAIL:Q2 |
| topshareQ | FAIL:M1 | PASS |
| wrapM | FAIL:M2 | PASS-noleafcall |
| wrapM3 | FAIL:M2 | PASS-noleafcall |
| wrapP | FAIL:M1 | PASS-noleafcall |
| wrapQ | FAIL:P3 | FAIL:P3 |
| leafM | FAIL:P3 | FAIL:P3 |

`leafP` is LEAF.

- The corpus chunks ran at cbae5d3a and on later split heads. They are not evidence for the amended controls; the
  ruling said so.
- **Conditions never seen as a first failure** (controls plus corpus): M1 appears, M2 appears, M3 appears; Q1, Q2, R1 and
  P1-P4 all appear; Q3 never appears. Q3 cannot be the first failure as implemented, because Q1 already defines `L` as a
  non-memory name. This is reported, not asserted, as the freeze requires.

## Jobs counted (33 successful disjoint leaf chunks; every one exit 0 with head = base)
Coverage was checked mechanically:
- the module lists of the 33 chunk files (read with `git show <sha>:Tests/Gaps/G8Census<NN>.lean`) are pairwise disjoint;
- their union is the 459 frozen modules minus the 6 unmeasured ones;
- each chunk's row count equals its logged `constants=` total.
| job | node | modules (count) | constants | log SHA-256 (prefix) |
|---|---|---|---|---|
| `g8-c00-cbae5d3a` | mkvs-dell | 1-40 (40) | 381 | `6e172d22883ac922` |
| `g8-c01-cbae5d3a` | mkvs-macpro | 41-80 (40) | 984 | `8ab67b515e4071fe` |
| `g8-c02a-7898e66e` | hayabusa | 81-100 (20) | 472 | `10fc745ce0c5f972` |
| `g8-c02ba-fe23d8c4` | hayabusa | 101-110 (10) | 243 | `d2bf9c58a29bce67` |
| `g8-c02bba-54d15a2d` | hayabusa | 111-115 (5) | 321 | `3855d152419707ad` |
| `g8-c02bbba-75674f7a` | hayabusa | 116-118 (3) | 80 | `a629ed8e19313f63` |
| `g8-c02bbbb-75674f7a` | hayabusa | 119-120 (2) | 39 | `b4a412ded1e2a6f8` |
| `g8-c03aaaa-54d15a2d` | mkvs-dell | 121-123 (3) | 135 | `c2a208ce771e4754` |
| `g8-c03aaaba-1763de04` | mkvs-dell | 124-124 (1) | 11 | `9d622eb1c18ed927` |
| `g8-c03aaabb-1763de04` | mkvs-dell | 125-125 (1) | 9 | `91e4b354d1375547` |
| `g8-c03aab-6bf559ed` | mkvs-dell | 126-130 (5) | 72 | `00137333c4071d1b` |
| `g8-c03ab-38c6c3b6` | mkvs-dell | 131-140 (10) | 150 | `c0ddd4cebe46fc05` |
| `g8-c03b-9c646bdb` | mkvs-dell | 141-160 (20) | 512 | `0b1918cfc8295866` |
| `g8-c04-cbae5d3a` | mkvs-macpro | 161-200 (40) | 1185 | `17623c06897dbf33` |
| `g8-c05-cbae5d3a` | hayabusa | 201-240 (40) | 1845 | `1efd0897cc9c9d9e` |
| `g8-c06-cbae5d3a` | mkvs-dell | 241-280 (40) | 2477 | `02ee05ab2327ea53` |
| `g8-c07aaaaa-41418c7d` | mkvs-dell | 281-282 (2) | 139 | `807395461b77eecb` |
| `g8-c07aaab-c9d828ed` | hayabusa | 284-285 (2) | 11 | `97630d2485e0b9ed` |
| `g8-c07aab-c6e52e31` | hayabusa | 286-290 (5) | 36 | `8807639108647e66` |
| `g8-c07ab-e7d2ab8e` | hayabusa | 291-300 (10) | 66 | `5b5d077a507f6c09` |
| `g8-c07b-09fda8c6` | hayabusa | 301-320 (20) | 155 | `50640c7b98a442f4` |
| `g8-c08-cbae5d3a` | hayabusa | 321-360 (40) | 647 | `1630803adf263552` |
| `g8-c09-cbae5d3a` | mkvs-dell | 361-400 (40) | 852 | `68df7aa930640580` |
| `g8-c10a-6917274f` | mkvs-dell | 401-420 (20) | 198 | `57f79946e3a73ce1` |
| `g8-c10baa-25fc476f` | mkvs-dell | 421-425 (5) | 64 | `9153d3d017a76b24` |
| `g8-c10baba-486fade3` | mkvs-dell | 426-428 (3) | 50 | `86cbc12564891822` |
| `g8-c10babbb-3cad56ae` | hayabusa | 430-430 (1) | 21 | `8e5f436494fa9831` |
| `g8-c10bb-8acaf690` | hayabusa | 431-440 (10) | 231 | `c54b458933daa449` |
| `g8-c11a-fb74ba71` | mkvs-macpro | 441-450 (10) | 157 | `9fdf9b079c2e7fb2` |
| `g8-c11baaa-c5cab928` | mkvs-dell | 451-452 (2) | 14 | `5ad316eeee653370` |
| `g8-c11babb-f19e88fc` | hayabusa | 455-455 (1) | 104 | `f4300458f1824541` |
| `g8-c11bbaa-9983cf65` | mkvs-dell | 456-456 (1) | 433 | `d16298ec6901e8c9` |
| `g8-c11bbbb-4bb630e4` | mkvs-macpro | 459-459 (1) | 40 | `a0c3cccc68f5f7a9` |

**Same name in two chunks:** 38 constant names appear in more than one chunk. Examples are `Sparkle.Core.Signal.Signal.ap.eq_1`,
lazily generated equation lemmas, `SparkleMem.sync.4.8` and `VerilogOutputs.*`. Each occurrence is a distinct constant of
a different module: these are exactly the clashes that prevent co-import. They are counted once per module, which
matches the per-module definition of U.

## Failed diagnostics (never counted)
**Import clashes:** the test modules MemNameCollisionTest, MemNameCollisionCertTest and MemNameCollisionProbe all define
`SparkleMem.sync.4.8`. Jobs:
- `g8-c02-cbae5d3a`, `g8-c02b-7898e66e`, `g8-c02bb-fe23d8c4`, `g8-c02bbb-54d15a2d`;
- `g8-c03-cbae5d3a`, `g8-c03a-9c646bdb`, `g8-c03aa-38c6c3b6`, `g8-c03aaa-6bf559ed`, `g8-c03aaab-54d15a2d`.

**An imported module fails to build:**
- `g8-c07-cbae5d3a`, `g8-c07a-09fda8c6`, `g8-c07aa-e7d2ab8e`, `g8-c07aaa-c6e52e31`, `g8-c07aaaa-c9d828ed`, `g8-c07aaaab-41418c7d`
  (module 283);
- `g8-c11-cbae5d3a`, `g8-c11b-fb74ba71`, `g8-c11ba-83bee56e`, `g8-c11baa-8437b7f7`, `g8-c11bab-8437b7f7`, `g8-c11bb-83bee56e`,
  `g8-c11bba-3eb1ebd6`, `g8-c11bbb-3eb1ebd6`, `g8-c11baab-c5cab928`, `g8-c11baba-f19e88fc`, `g8-c11bbab-9983cf65`,
  `g8-c11bbba-4bb630e4`.

**Census-process OOM at 12Gi (exit 137, after all imports were built):**
- `g8-c10-cbae5d3a`, `g8-c10b-6917274f`, `g8-c10ba-8acaf690`, `g8-c10bab-25fc476f`, `g8-c10babb-486fade3`;
- `g8-c10babba-3cad56ae` (module 429 alone).

**Tool build failures, before any measurement:**
- `g8-ctl-b481c4d8` (shadowed `let`);
- `g8-ctl-c1cd44bd` (`HashMap.foldl`, MetaM lift);
- `g8-ctl-1e4807b0`: the Amendment 2 contradiction, plus a doc comment before `run_meta`.

## Deviations from the first-written plan (all recorded on the Issue when they happened)
1. **Q1-noleafcall control contradiction:** resolved by Amendment 2. The wrapper controls accept `PASS-noleafcall`; T0 is
   unchanged.
2. **Census-process OOM:** the first-written split rule named import failures only. Amendment 3 extends recursive halving
   to OOM at 12Gi, makes a single-module OOM UNMEASURED, and keeps OOM jobs as failed diagnostics.
3. **Split chunks run at later heads.** Each split commit only adds chunk files and lakefile entries; the tool is
   unchanged since cbae5d3a.
   - Each batch ran from its own detached worktree, pinned at the commit its job name carries.
   - The original chunk worktree was re-pinned to cbae5d3a after a docs commit, so no queued chunk ran under a mislabelled
     head.
4. **Placement:** the control job `g8-ctl-0df300dc` shared mkvs-dell with chunk c00, the only time two heavy builds ran on one node. Every other split batch ran one job per node, in sequence on a node.
5. **Runner incident:** the wait loop of my launch wrapper matched its own command line, so the split queues did not
   start. It was killed while it was only sleeping. No kjob job was affected or cancelled.

## Evidence outside the source tree
These are not committed, because logs and measurement data stay out of the source tree.
- `~/git/.kjob-state/g8_census_rows.tsv`: all 12134 rows (decl, kind, category, class, M, Q, chunk). SHA-256
  `c0edfc48d4462c70e4de6ba938d59938041352530ff19a39a2c2877977309673`.
- `~/git/.kjob-state/g8_leaf_jobs.txt`: the 33 counted jobs. SHA-256 `0eaf1187e3006cbb985856c580484bb2409c23b8dfdcf7a83838a1ef62284cfa`.
- `~/git/.kjob-state/g8_agg.py` and `g8_census_agg.json`: the aggregation script and its output.
- Per-job logs: `~/git/.kjob-state/namespaces/sparkle-dev/<job>/output.log`, with SHA-256 prefixes in the table above. Each
  chunk's rows and totals are also stored as the `String` constants `G8Census.c<NN>.{rows,totals}` in its olean.

## Not claimed
- T0-eligible is not membership. No new member is claimed.
- `group` (QuadGroupFacts) and the GEN-SHAPE fields are not evaluated.
- A T0 FAIL is a non-membership only relative to the MachineDefines shape tie.
- Nothing is claimed about the 6 unmeasured modules, the 3 non-lake files, or inputs outside the frozen corpus list.
- In particular, "no IP/Examples candidate" and "every IP parent fails T0" hold only for the measured modules. They are
  not claimed for `Tests.IP.Net.TCPHeaderTest` (module 429, census OOM) or any other unmeasured module.
- No compiler change and no CI.
