# B — the leaf sweep at the DESIGN level, as a measured unit (round par/b-31)

Branch `par/b-31` from `poc/roundtrip-proof` 11e3944b. Worker B.

**NOTHING HERE IS BUILT OR RUN.** No `lean`, `lake` or simulator was started.
Every file is WRITTEN, NOT BUILT. **No endpoint is claimed to exist**: every
outcome below is PREDICTED by reading; the sweep files assert none of it.

Marks: **[R]** read at 11e3944b; **[B]** asserted by a test that is in
`Tests.AllTests` (built per the integration records, not re-run);
**[P]** predicted.

## 0. Files

| file | content |
|---|---|
| `Tools/ShippingLeafSweepCommand.lean` | `#leaf_sweep f` (never an error), `#leaf_sweep_summary` (an error only on an inconsistency of what the file measured) |
| `Tests/Compiler/LeafSweep<Group>Test.lean` × 15 | one group each, TARGET-ONLY |
| `docs/parallel/B-leaf-sweep.md` | this file |

No existing file was changed. A non-throwing form did not exist:
`#machine_leaf_design_try f "CLASS"` [R `Tools/ShippingLeafDesignCommand.lean`
354–359] is an error when the class is not the written one; the function
under it, `leafDesign`, never throws and restores the environment on
REFUSED / FAILED [R 307–333]. `#leaf_sweep` calls that function.

## 1. Where "≈ 48" came from, and the list

`docs/parallel/A-leaf-gen.md` §5 [R]: the `#machine_endpoint` lines of the
built test files (plus `ShippingMachineFuseTest`'s programmatic three),
classified by `grep` of the definition; "predicted in 54 (register: 7 of
them run in this round's test incl. `cnt`)". 54 − 7 = 47; with `shift3`
(`DepthRegsChildTest`, later) the count below is 48. I re-read every
definition's file for the kind (`circuit do` / `Signal.loop` / `runCircuitH`
/ none) and the exact name; I did not run the reader.

The scope of `#machine_leaf_design` (the scan of
`Tools.ShippingLeafEntryCommand.scan` [R 162–208], in this order): the
machine reader accepts `f`; no call entry (else REFUSED "memory" if an entry
is a memory placeholder, "has calls" otherwise); at least one register slot
(else REFUSED "slotless"); `f.machineData / machine_ok / machine_body` exist;
`f.machine_ships_wired` exists. Then `f.machine_closes` must be derivable
(`closesTheorem?`; else REFUSED), and the generated proof must check (else
FAILED).

`f.machine_ships_wired` is made by `#machine_endpoint` for a declaration
with a slot and without calls "and leaves the endpoint as it was when its
four structural premises are not decided" [R scan's message 207;
`Tools/ShippingMachineCommand.lean` 2599–2642]. Whether it EXISTS for a
given declaration is a build fact; column "wired" says what a built test
asserts about it.

### 1a. Register leaves — 48 candidates (covered ones excluded: `cnt`, `acc`, `pe`, `twoHW`, `toggle`, `loopPair`, `toggleL`)

| # | declaration (full name) | defined in | kind [R] | wired | PREDICTED | sweep file |
|---|---|---|---|---|---|---|
| 1–2 | `reflSharedLet`, `reflAliasLet` (root level) | `Tests/Compiler/ShippingReflectCtxTest.lean` 118, 129 | `circuit do`, one 8-bit register, `let`s | not asserted | GENERATED | `Closes` |
| 3–5 | `closesInputLet`, `closesOpAlias`, `closesChain` (root level) | `Tests/Compiler/ShippingMachineClosesTest.lean` | the same | not asserted; `machine_closes` asserted present (A-leaf-gen §5) | GENERATED | `Closes` |
| 6 | `Sparkle.Tests.Compiler.ShippingMachineEntryTest.mThree` | `ShippingMachineEntryTest.lean` 43 | `circuit do`, three slots | [B] (`ShippingMachineCommandTest` 215) | GENERATED | `Entry` |
| 7–8 | `….ShippingMachineEntryTest.twoFlag`, `twoCnt` | 69, 70 | a FIELD of `twoHW`'s structure result | logged count only | GENERATED | `Entry` |
| 9–10 | `….ShippingMachineEntryTest.linChk`, `linChkDefault` | 74, 80 | the LIN checksum, generic / default domain | logged count only | GENERATED | `Entry` |
| 11 | `Sparkle.IP.Bus.LINHW.checksumHW` | `IP/Bus/LINHW.lean` 111 | IP module, register | logged count only | GENERATED | `Entry` |
| 12 | `Sparkle.IP.Crypto.EcdsaSignDemo.wMulN` | `IP/Crypto/EcdsaSignDemo.lean` 88 | `@[hardware_module]` wrapper of a 256-bit FSM | [B] (216) | GENERATED; cost of the decides NOT known | `Crypto256` |
| 13–14 | `Sparkle.IP.Crypto.P256SignDemo.wMul`, `wMulN` | `IP/Crypto/P256SignDemo.lean` 34, 38 | the same | logged count only | GENERATED; cost NOT known | `Crypto256` |
| 15–16 | `Sparkle.IP.Crypto.EcdsaSignDemo.wTx`, `Sparkle.IP.USB.Fido2Demo.wTx` | `EcdsaSignDemo.lean` 305, `IP/USB/Fido2Demo.lean` 54 | UART transmitter wrappers | logged count only | GENERATED | `Uart` |
| 17–18 | `….ShippingMachineLoopTest.wholeLoop`, `wholeToggle` | `ShippingMachineLoopTest.lean` 69, 74 | `Signal.loop` as the whole value | logged only | GENERATED | `Loop` |
| 19–20 | `….ShippingMachineLoopTest.counterLoop`, `accLoop` | 32, 43 | `Signal.loop`, 2 / 1 registers | [B] (121–123) | GENERATED | `Loop` |
| 21 | `….ShippingMachineLoopTest.divQ` | 89 | a projection of an `@[reducible]` `Signal.loop` engine | logged only | GENERATED | `Loop` |
| 22 | `Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController` | `IP/YOLOv8/Blocks/Bottleneck.lean` 109 | `Signal.loop`, 4 slots | logged only | GENERATED | `LoopIP` |
| 23 | `Sparkle.IP.RV32.Divider.dividerSignal` | `IP/RV32/Divider.lean` 230 | `Signal.loop`, 8 slots | [B] | GENERATED; cost NOT known | `LoopIP` |
| 24–28 | `….ShippingMachineNestTest.latch2`, `loopBack`, `front`, `pair`, `consumer` | `ShippingMachineNestTest.lean` 34–87 | nested sub-machines flattened (head `_of_nested`) | [B] all five (137–141) | GENERATED | `Nest` |
| 29–35 | `….ShippingMachineNormTest.nConst`, `nLit`, `nMixed`, `nLift`, `nNot`, `nMapNot`, `nSlice` | `ShippingMachineNormTest.lean` 42–103 | `circuit do` register through the normal form | not asserted | GENERATED | `Norm` |
| 36–40 | `Sparkle.Tests.RunCircuitHTest.counterH`, `twoCountH`, `mixedWidthH`, `tripleCountH`, `fourCountH` | `Tests/RunCircuitHTest.lean` 26–71 | `runCircuitH` counters, NO input | not asserted | GENERATED (an input-free entry was never run through the leaf generators) | `Raw` |
| 41 | `Sparkle.Tests.CircuitDoTest.pairCounterCdo` | `Tests/CircuitDoTest.lean` 141 | `circuit do` pair counter | not asserted | GENERATED | `Raw` |
| 42 | `….ShippingMachineRawTest.tupReg` | `ShippingMachineRawTest.lean` 71 | `circuit do` register, a tuple-typed input (one packed port) | not asserted | GENERATED | `Raw` |
| 43–45 | `….ShippingMachineTeleTest.divInLoop`, `chain2`, `chain3` | `ShippingMachineTeleTest.lean` 72, 42, 52 | telescope (head `_of_tele_ext`) | not asserted | GENERATED | `Tele` |
| 46–47 | `….ShippingMachineFuseTest.outer`, `siblings` | `ShippingMachineFuseTest.lean` 25, 34 | fused nested `Signal.loop`s; endpoint by `generate (checkCloses := false)` | not asserted | NOT PREDICTED: REFUSED ("no machine_ships_wired", or "MachineCloses is not derived") or GENERATED | `Fuse` |
| 48 | `Sparkle.Tests.Compiler.DepthRegsChildTest.shift3` | `DepthRegsChildTest.lean` | a bare-register chain (head `_of_regs`) | not asserted | GENERATED | `Regs` |

PREDICTED totals: GENERATED 46, not predicted 2. For the 34 rows without a
[B] "wired", GENERATED is conditional on `f.machine_ships_wired` existing; if
not, the line is REFUSED "no … machine_ships_wired" — a fact about the
ship-level endpoint, not a defect of this generator.

### 1b. Predicted refusals swept too (cheap: the scan only)

| declarations | defined in | PREDICTED | why |
|---|---|---|---|
| `….ShippingMachineRawTest.negSig`, `negLift`, `addThree`, `useHalf`, `triBundle`, `tupFst`, `tupMapFst`, `tupSum`, `tupHwLet3` (9) | `ShippingMachineRawTest.lean` 24–78 | REFUSED slotless | [R] no `Signal.reg` / `Signal.register` / `Signal.loop` in the body: no register slot (`LeafKid.slots` asks one) |
| `….ApplicativeSemanticsTest.reversed`, `reversedSurface`, `nestedSurface`, `constantRight`, `constantLeft`, `duplicate`, `withConstant`, `nested`, `complement`, `concatReverse`, `orderedLess`, `rightAssociated`, `permutedFour` (13) | `ApplicativeSemanticsTest.lean` | REFUSED slotless | combinational by A-leaf-gen §5's grep; the bodies were NOT re-read by me |
| `….ShippingMachineCombTest.pickByte`, `Sparkle.IP.Net.IPv4.ipv4HeaderByte`, `ipv4HeaderChecksumSig`, `Sparkle.IP.Net.HTTP.httpGetByte` (4) | `ShippingMachineCombTest.lean`, `IP/Net/IPv4.lean` 213, 163, `IP/Net/HTTP.lean` 86 | REFUSED slotless | the same source; not re-read |
| `….ShippingSignOpsTest.sext`, `ashrK`, `shiftSurface`, `ashrSig`, `scaleMul`, `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize` (6) | `ShippingSignOpsTest.lean`, `IP/YOLOv8/Primitives/Requantize.lean` 60 | REFUSED slotless | the same source; not re-read |
| `….ShippingMachineTeleTest.hftByte` | `ShippingMachineTeleTest.lean` 65 | REFUSED has calls | [R] "the emitter calling the `@[hardware_module]` byte table inside its body": a call entry |
| `….ShippingMachineFuseTest.withMemory` | `ShippingMachineFuseTest.lean` 42 | REFUSED memory | [R] `Signal.memoryComboRead` twice: a memory is an instance of a memory-only submodule, so the shape has call entries that are memory placeholders |

PREDICTED totals: slotless 32, has calls 1, memory 1.

All 82 swept: PREDICTED GENERATED 46 / REFUSED 34 / not predicted 2.

Not swept: declarations without `#machine_endpoint` (helpers `latch`,
`stage`, `source`, `detect`, `countOn`, `innerCnt`: predicted REFUSED "no
machine endpoint"); every parent (calls); the Keccak declarations (parents);
the corpus list of `scripts/shipping-coverage` (exists only as the output of
a run).

## 2. The command (`Tools/ShippingLeafSweepCommand.lean`)

`#leaf_sweep f`, per declaration, in this order:

1. `LEAFSWEEP START f` — `IO.eprintln` (stderr, at once) AND a message;
2. the generator `leafDesign f` (the scan; `closesTheorem?`;
   `leafKidTheorem`; the endpoint term; `checkStatement`; `addOrCompare`;
   `collectAxioms` on the endpoint, `machine_leafKid`, `machine_closes`);
3. `LEAFDESIGN DATA …`, the premise listing, `LEAFDESIGN <class> f: <reason>`;
4. when a theorem was made: `Tools.ShippingLeafDesignCommand.audit f` (logs
   its listing, then asserts the two binders, the one antecedent `ChildBnd`,
   0 NOT ALLOWED, no check / guard / checker constant, `DesignSV` over
   `childMap`; standard axioms of the endpoint and of the seven general
   theorems) — its exception is CAUGHT and recorded; then the parents' gap
   tool `Tools.ShippingFinalGoalCommand.gapOf` (adds `…_leaf0_gap`; the
   `gap_…` binder names are logged; a failure is caught and recorded);
5. `LEAFSWEEP RESULT f: …; <ms> ms` and a row in an `IO.Ref`.

It never throws (an unresolved identifier is `UNRESOLVED`).

`#leaf_sweep_summary`: `LEAFSWEEP ROW` per declaration, `LEAFSWEEP SUMMARY`
with the counts by class; an ERROR only when (a) a GENERATED / REBUILT row's
audit is not `OK`, or its listing has a NOT ALLOWED line, or the theorem is
not in the environment; (b) another row left `machine_design_leaf0` behind;
(c) nothing was swept. These are consistency checks of what the same file
just measured. No class and no count is expected by any file.

The classifier is the existing `Tools.ShippingFinalGoalCommand.allowed`,
through the generator's own `checkStatement` and `audit` (the same function
`Tests.Compiler.NoPortsTest.premiseLines` uses; that test-side helper is not
imported, to keep each file's closure to its one source test).

## 3. The test files (all TARGET-ONLY; nothing added to `AllTests`)

Each: its source test file(s) + `Tools.ShippingLeafSweepCommand`; one
`set_option maxHeartbeats 0 in #leaf_sweep <full name>` per declaration;
`#leaf_sweep_summary`. The declaration sets are pairwise disjoint.

| file `Tests/Compiler/…` | imports | declarations | n |
|---|---|---|---|
| `LeafSweepClosesTest` | `ShippingMachineClosesTest` | rows 1–5 | 5 |
| `LeafSweepEntryTest` | `ShippingMachineCommandTest` | rows 6–11 | 6 |
| `LeafSweepCrypto256Test` | `ShippingMachineCommandTest` | rows 12–14 | 3 |
| `LeafSweepUartTest` | `ShippingMachineCommandTest` | rows 15–16 | 2 |
| `LeafSweepLoopTest` | `ShippingMachineLoopTest` | rows 17–21 | 5 |
| `LeafSweepLoopIPTest` | `ShippingMachineLoopTest` | rows 22–23 | 2 |
| `LeafSweepNestTest` | `ShippingMachineNestTest` | rows 24–28 | 5 |
| `LeafSweepNormTest` | `ShippingMachineNormTest` | rows 29–35 | 7 |
| `LeafSweepRawTest` | `ShippingMachineRawTest` | rows 36–42 | 7 |
| `LeafSweepTeleTest` | `ShippingMachineTeleTest` | rows 43–45, `hftByte` | 4 |
| `LeafSweepFuseTest` | `ShippingMachineFuseTest` | rows 46–47, `withMemory` | 3 |
| `LeafSweepRegsTest` | `DepthRegsChildTest` | row 48 | 1 |
| `LeafSweepSlotlessRawTest` | `ShippingMachineRawTest` | 9 slotless | 9 |
| `LeafSweepSlotlessApplicativeTest` | `ApplicativeSemanticsTest` | 13 slotless | 13 |
| `LeafSweepSlotlessMiscTest` | `ShippingMachineCombTest`, `ShippingSignOpsTest` | 10 slotless | 10 |

The two groups whose kernel cost is unknown (`Crypto256`, `LoopIP`) are
apart, so a slow 256-bit wrapper or the 8-slot divider blocks at most two
other declarations. The three slotless files exceed "8 per file" on purpose:
a refusal is the scan only.

### Build order

`lakefile.lean` (not edited):

```lean
lean_lib «Tools.ShippingLeafSweepCommand» where
  roots := #[`Tools.ShippingLeafSweepCommand]
```

1. `Tools.ShippingLeafSweepCommand` (imports the built
   `Tools.ShippingLeafDesignCommand`, `Tools.ShippingFinalGoalCommand`).
2. The cheapest first, to validate the command itself:
   `Tests.Compiler.LeafSweepSlotlessRawTest` (refusals only), then
   `LeafSweepClosesTest` (five small `circuit do` machines).
3. Then in any order, one target at a time: `Nest`, `Norm`, `Entry`, `Loop`,
   `Raw`, `Tele`, `Regs`, `Fuse`, `Uart`, the other two `Slotless…`.
4. Last, alone: `LoopIP`, `Crypto256`.

A sweep file's success means only "the command ran and what it measured is
consistent"; READ THE LOG for the classes.

### How to read the log

    grep -E "LEAFSWEEP (START|RESULT|ROW|SUMMARY)|LEAFDESIGN (GENERATED|REBUILT|REFUSED|FAILED)"

* a `START` without a `RESULT`: that declaration hung or was killed (the
  stderr `START` is printed before anything else of the command);
* `LEAFDESIGN REFUSED f: slotless … / has calls … / memory … / no … machine_ships_wired … / MachineCloses is not derived …`: out of scope, with the reason;
* `LEAFDESIGN FAILED f: …`: in scope by the scan, but a generated proof or
  the statement check failed — a FINDING, with the first two error messages;
* `LEAFSWEEP RESULT f: GENERATED; premise lines listed N, NOT ALLOWED 0;
  audit OK; gap hypotheses []; …; <ms> ms`: the theorem was added and
  kernel-checked, its premise list is the `LEAFDESIGN PREMISE` /
  `LEAFDESIGN AUDIT PREMISE` lines above it (PREDICTED: two binders — the
  run, `MachineDefines f` — and one antecedent `ChildBnd`; that count is
  asserted by the generator's own check, not written in a sweep file);
* `audit FAILED: …` or `gap tool FAILED: …` in a RESULT line: recorded; the
  first makes `#leaf_sweep_summary` an error.

### The scope sentence each GENERATED line carries (binding)

"`f.machine_design_leaf0` for ONE declaration `f` as an entry, depth 0, no
call: data conditions decided for `f` (conditions, not reductions); the run,
the reflection `MachineDefines f` and the runtime boundary `ChildBnd` stay
premises; the conclusion is `DesignSV` of the module list over the returned
design's child map — not the SV string, not `#sim`; a compiler with the two
guards of `Sparkle/IR/RefineCheck.lean`." It says nothing about the
declaration as a CHILD of a parent, about any other declaration, or about a
slotless leaf.

## 4. What could enter `AllTests` later, and at what cost

None is added now. After a clean run:

* the nine register groups with small machines (`Closes`, `Entry`, `Loop`,
  `Nest`, `Norm`, `Raw`, `Tele`, `Regs`, `Uart`) could be added — they add
  only `f.machine_design_leaf0[_gap]` and, where absent, `f.machine_leafKid`
  / `f.machine_closes`; no other test in `AllTests` generates these for the
  same declarations [R: grep of `machine_design_leaf0` / `leafKidTheorem`
  users — `LeafEntryFamilyTest`, `LeafDesign*Test` on the seven covered
  ones, and parents' tests on their own children `cnt`, `acc`, `shift3`, …;
  `DepthRegsChildTest` mentions `machine_leafKid`; if `shift3.machine_leafKid` exists there it is REUSED, not re-added — which of the two holds I did not determine]. To
  make them regression tests they would first be rewritten with the MEASURED
  classes (`#machine_leaf_design_try f "GENERATED"`), since a sweep asserts
  no class;
* expected cost per declaration [P, from `B-leaf-design.md` §8 and
  `A-leaf-gen.md` §6]: six data `decide`s of `leafKidTheorem`, one
  application whose statement is about three times `machine_ships_leafC`'s,
  the audit's `collectAxioms` on ten constants, the gap theorem — "seconds"
  for the small machines by analogy with the seven built ones, NOT measured;
  the `ms` field of each RESULT line measures it;
* `Crypto256`, `LoopIP`: only after their cost is known;
* the three `Slotless…` files and `Fuse`: of no value as regression tests
  beyond the four refusals `LeafDesignFamilyTest` already asserts.

## 5. Risks (unbuilt), in order

1. `initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]` read by a command
   elaborated in a downstream file (pattern: `fuseOrderRef`,
   `Tools/ShippingMachineCommand.lean` 2087).
2. `let x : T ← try … catch …` with an `if … then … else` chain inside the
   `try` (three places), and a structure instance as the `catch` result.
3. `audit f` after GENERATED asserts that `f.machine_ships_wired` mentions
   the three check constants [R 401–404]; for a head other than the seven
   built ones' this may not hold — it would show as `audit FAILED` and make
   the summary an error for that file (a finding, but it fails the target).
4. Names: 82 identifiers typed from the sources; a wrong one is logged
   `UNRESOLVED`, not an error.
5. `gapOf` on an endpoint of this shape built only for the seven.
6. An input-free entry (`counterH` …), a tuple-typed input (`tupReg`), a
   projection of a structure result (`twoFlag`), heads `_of_nested`,
   `_of_tele_ext`, `_of_regs`: none was run through `leafKidTheorem` /
   `leaf_entry_design0_of_wired` before — FAILED lines here are the point of
   the sweep.

## 6. What I could not determine by reading

* For 34 of the 48, whether `f.machine_ships_wired` exists (column "wired").
* For `outer`, `siblings`: whether `machine_closes` is derivable and the
  wired form exists (their endpoints were generated with
  `checkCloses := false`).
* Whether the bodies of the 23 slotless declarations outside
  `ShippingMachineRawTest` are register-free (taken from A-leaf-gen §5).
* Kernel time and memory of any declaration.
* Whether `machine_leafKid`'s six decides hold on the new shapes.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `fd3f89dccd1c5d0957c2b5f9dff3ded976955f83` (poc 11e3944b + these files), cgrun 3 GiB swap 0, worker's files unchanged, first
attempt. `b31-sweep`: the command, then each of the fifteen groups alone (each 2–4 s wall, exit 0; peak
0.79 GB; logs in `~/sparkle-work/leaf-sweep/`). `b31-all`: `Tests.AllTests` with the twelve register-leaf
groups imported (the three `Slotless…` files stay target-only), 1307 jobs, exit 0, peak 0.44 GB.

Result over the 82 declarations: GENERATED 48, REFUSED 34, FAILED 0, UNRESOLVED 0. (Predicted: 46 / 34 /
2 not predicted — the two not predicted, `outer` and `siblings`, generated.)

Each GENERATED row: `f.machine_design_leaf0` in the environment; the generator's listing has 3 premise
lines — binder `hr` (the run of `synthesizeCombinational f`), binder `entry` (`MachineDefines f`),
antecedent under the existential `ChildBnd` — 0 NOT ALLOWED; the generator's audit (standard axioms, no
checker constant) passed; gap hypotheses `[]`; 150–640 ms each.
SCOPE of each: one declaration, depth 0, data conditions decided per declaration, runtime boundary,
`DesignSV` of the module list — not the SV string, not `#sim`, not all successful inputs.

GENERATED (48):
```
Sparkle.IP.Bus.LINHW.checksumHW
Sparkle.IP.Crypto.EcdsaSignDemo.wMulN
Sparkle.IP.Crypto.EcdsaSignDemo.wTx
Sparkle.IP.Crypto.P256SignDemo.wMul
Sparkle.IP.Crypto.P256SignDemo.wMulN
Sparkle.IP.RV32.Divider.dividerSignal
Sparkle.IP.USB.Fido2Demo.wTx
Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController
Sparkle.Tests.CircuitDoTest.pairCounterCdo
Sparkle.Tests.Compiler.DepthRegsChildTest.shift3
Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChk
Sparkle.Tests.Compiler.ShippingMachineEntryTest.linChkDefault
Sparkle.Tests.Compiler.ShippingMachineEntryTest.mThree
Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoCnt
Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoFlag
Sparkle.Tests.Compiler.ShippingMachineFuseTest.outer
Sparkle.Tests.Compiler.ShippingMachineFuseTest.siblings
Sparkle.Tests.Compiler.ShippingMachineLoopTest.accLoop
Sparkle.Tests.Compiler.ShippingMachineLoopTest.counterLoop
Sparkle.Tests.Compiler.ShippingMachineLoopTest.divQ
Sparkle.Tests.Compiler.ShippingMachineLoopTest.wholeLoop
Sparkle.Tests.Compiler.ShippingMachineLoopTest.wholeToggle
Sparkle.Tests.Compiler.ShippingMachineNestTest.consumer
Sparkle.Tests.Compiler.ShippingMachineNestTest.front
Sparkle.Tests.Compiler.ShippingMachineNestTest.latch2
Sparkle.Tests.Compiler.ShippingMachineNestTest.loopBack
Sparkle.Tests.Compiler.ShippingMachineNestTest.pair
Sparkle.Tests.Compiler.ShippingMachineNormTest.nConst
Sparkle.Tests.Compiler.ShippingMachineNormTest.nLift
Sparkle.Tests.Compiler.ShippingMachineNormTest.nLit
Sparkle.Tests.Compiler.ShippingMachineNormTest.nMapNot
Sparkle.Tests.Compiler.ShippingMachineNormTest.nMixed
Sparkle.Tests.Compiler.ShippingMachineNormTest.nNot
Sparkle.Tests.Compiler.ShippingMachineNormTest.nSlice
Sparkle.Tests.Compiler.ShippingMachineRawTest.tupReg
Sparkle.Tests.Compiler.ShippingMachineTeleTest.chain2
Sparkle.Tests.Compiler.ShippingMachineTeleTest.chain3
Sparkle.Tests.Compiler.ShippingMachineTeleTest.divInLoop
Sparkle.Tests.RunCircuitHTest.counterH
Sparkle.Tests.RunCircuitHTest.fourCountH
Sparkle.Tests.RunCircuitHTest.mixedWidthH
Sparkle.Tests.RunCircuitHTest.tripleCountH
Sparkle.Tests.RunCircuitHTest.twoCountH
closesChain
closesInputLet
closesOpAlias
reflAliasLet
reflSharedLet
```
REFUSED (34), by reason:
```
      1 has calls 
      1 memory
     32 slotless
```
The sweep files assert consistency of what they measured (a GENERATED row has its theorem, a passing audit
and 0 NOT ALLOWED); they do NOT yet assert the class per declaration, so a GENERATED → REFUSED regression
would not fail the suite. Asserting forms are a follow-up.
