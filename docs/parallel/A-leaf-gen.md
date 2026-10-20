# A / G1: the generator for leaf register machines as entries (round par/a-32)

Branch `par/a-32`, base `fix/opt-print-guard-build` `be0c5bbc` (poc `cfbab0db`
+ the two compiler guards + `Tools/ShippingGuardsLeaf.lean`).
**WRITTEN, NOT BUILT.** Nothing here was built or run; no premise counts as
removed until the integrator's build. Marks: **[R]** read in the source at
that commit, **[P]** predicted (a value no one has computed), **[I]**
inferred.

Files (all new):

| file | what |
|---|---|
| `Tools/ShippingLeafEntryCommand.lean` | `#machine_leaf_entry f`, `#machine_leaf_entry_try f "GENERATED\|REBUILT\|REFUSED\|FAILED"`; `scan`, `endpointTerm`, `checkStatement`, `audit`, `sweep` |
| `Tests/Compiler/LeafEntryFamilyTest.lean` | compare path on `cnt`; six GENERATED + audit; four REFUSED |
| `docs/parallel/A-leaf-gen.md` | this note |

## 1. The command

For a machine declaration WITHOUT calls and WITH a register slot whose
`f.machine_ships_wired` exists, `#machine_leaf_entry f` adds

    f.machine_ships_leafC :
      ∀ {mctx mref cctx cref w w' b design}
        (hbnd : ChildBnd mref cref w)
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref f f.machineData.shape),
        ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          MachineShips f f.machineData (dropZeroWidthModule raw) b (checkedOptimize b)
            (wofOf (checkedOptimize b)) dom src

with the proof term of `LeafEntryCntClosedTest` (built in isolation on
`cnt`), over generated constants:

    fun hbnd hr entry =>
      Tools.ShippingLeafEntry.leaf_entry_ships_of
        (f.machine_ships_wired hr entry (f.machine_closes mctx mref cctx cref))
        (Tools.ShippingGuardsLeaf.leaf_entry_textChecks_closed
          (f.machine_leafKid entry) hbnd hr)

The term is built in `MetaM` (`endpointTerm`): the binders are those of
`f.machine_ships_wired` (11 expected: four contexts, two worlds, module,
design, run, `MachineDefines`, `MachineCloses`), `hbnd` is added, the
`MachineCloses` binder is replaced by `f.machine_closes` at the contexts
(its statement is compared with the binder by `isDefEq` first). The
STATEMENT is the inferred type of the term; `dom` and `src` are never
written.

Differences from the hand-built term: `leaf_entry_textChecks_closed` instead
of `leaf_entry_textChecks_bnd … (mergeReg_closed b) (leaf_entry_optPrint …)`
— the same theorem by its one-line proof [R `Tools/ShippingGuardsLeaf.lean`
150–153]; and no reference to `mergeChecked_keeps_reg` /
`…_keeps_nonAssign` (the rename does not touch these files).

### Why not `leaf_entry_ships_closed` literally

`leaf_entry_ships_closed` takes `soundL` (the wired twin of the endpoint's
head with its arguments) and re-applies `machine_ships_wired`.
`#machine_endpoint` already stored that as `f.machine_ships_wired`
(`Tools/ShippingMachineCommand.lean` 2619–2639 [R]): the four structural
premises decided, and — for a transported endpoint — the source retargeted
(`retarget`, an `Eq.mpr`). Using the stored theorem needs no table of heads,
is right for a transported endpoint (a `soundL` rebuilt from
`machine_sound`'s arguments would be about the inlined source), and decides
nothing twice. This is what `LeafEntryCntClosedTest` did ("built with the
leafB proof term") [R].

### What it adds, and the compare path

* `f.machine_closes` when absent: the built `closesTheorem?` (a refusal where
  the data do not give it).
* `f.machine_leafKid` when absent: the built `leafKidTheorem`. That built
  generator returns an existing `machine_leafKid` unchanged — it is not this
  round's generator, and the theorem is a data theorem whose statement `f`
  fixes. Logged as `EXISTING before this command (not regenerated)`.
* `f.machine_ships_leafC`. If it exists: rebuilt, added as
  `f.machine_ships_leafC_regen` (kernel-checked), statements required
  `isDefEq`, an error otherwise (`Tools.ShippingNoPortsKidsCommand.addOrCompare`,
  built). Never a silent return.

Before adding, `checkStatement`: exactly three proposition binders (one
`RunsTo`, one `MachineDefines` whose declaration is `f`, one `ChildBnd`), all
ALLOWED by `Tools.ShippingFinalGoalCommand.allowed`; none of `simpleBody`,
`seqCheck`, `seqNames`, `MachineCloses`, `InvW`, `printOk`, `isAssign`; the
conclusion mentions `MachineShips` and `wofOf`. A statement failing this is
not added.

## 2. Restated vs imported

| what | state |
|---|---|
| `leaf_entry_ships_of`, `leaf_entry_textChecks_closed`, `LeafKid`, `leafKidTheorem`, `closesTheorem?`, `addOrCompare`, `readMachine`, `allowed`, `machine_ships_wired` | IMPORTED, used as built. No theorem is restated |
| a new proof | NONE. The command is plumbing over built theorems |
| the audit of `LeafEntryCntClosedTest` §3 | RESTATED as `Tools.ShippingLeafEntryCommand.audit` (generic in `f`; the test's code with the declaration a parameter, and the `MachineDefines` binder checked to be about `f`) |
| `noAsync` | RESTATED (two lines; `private` in the three files that have it) |

## 3. Scope and the refusal table (`scan`)

`scan` adds nothing and never throws. Order of the tests:

| # | condition | outcome line (condensed) | which generator applies instead |
|---|---|---|---|
| 1 | `readMachine f` throws | REFUSED: not a machine declaration — the reader's own message | gate route: `#gate_child`; legacy route: none |
| 2 | a call entry with `memChild? ≠ none` | REFUSED: memory — the memory is an INSTANCE of a memory-only submodule, `f` is a parent | `#machine_composedT`, then `generateM0` (`Tests/Compiler/NoPortsMemOnly*Test`), or `#machine_no_ports_kids` with a sequential child |
| 3 | any other call entry | REFUSED: has calls | `#machine_design_svHR` + `#machine_closes_at` + `#machine_oneout` (one-output gate children); `#machine_design_svNR f n` + `#machine_no_ports` / `_kids` / `_seq` / `_deep` |
| 4 | no register slot | REFUSED: slotless — endpoint `machine_ships_comb` (`simpleBody b = true`), not covered: no theorem gives `simpleBody` of a closed machine; the assign-only merge is `mergeDuplicates`' own, not print-guarded; the simple branch keeps a candidate under `optCheck`, whose print conjunct is `PrintCheck.moduleCheck`, not `printOk` (`A-leaf-entry.md` §6) | none |
| 5 | `f.machineData` / `machine_ok` / `machine_body` missing | REFUSED: no machine endpoint | `#machine_endpoint f` first |
| 6 | `f.machine_ships_wired` missing | REFUSED: names the head of `f.machine_sound` (and `TRANSPORTED` if under `Eq.mpr`) | — (`generateCore` did not make the wired form: its progress line says why) |
| 7 | `f.machine_closes` neither there nor derived | REFUSED: `MachineCloses` not derived from the data (`letsOk`) | — |
| — | a `LeafKid` condition fails at its `decide`; the wired statement has other binders; the statement check fails | FAILED, with the generated theorem's error | — |

On REFUSED / FAILED the environment and the message log are put back.

### The loop-leaf finding

Asked: does `leaf_entry_ships_*` take any `MachineTraceL` endpoint or only
`_of_data`? **Any.** [R] `soundL` in `leaf_entry_ships_closed`
(`Tools/ShippingGuardsLeaf.lean` 173–200) and in `machine_ships_wired`
(`Tools/ShippingMachineShipsW.lean` 41–63) is

    RunsTo (synthesizeCombinationalCore f [] false) … → MachineDefines … → MachineCloses … →
      MachineTraceL f d m design dom src (fun _ _ bits => bits) lsrc

with no mention of how it was proved. And the check side
(`leaf_entry_textChecks_closed`) does not take `soundL` at all: it reads
`LeafKid` — data conditions, the reflection, the closing — and the run;
`leaf_run_typedIn_bnd` goes through `synthesizeCombinationalCore_machine_sound`
and `closeMachine_typed`, the same for every machine shape [R
`Tools/ShippingLeafEntryBnd.lean` 69–304].

So NOT refused: loop-built (`machine_trace_of_loop` / `_of_regs`), nested
(`_of_nested`), telescope (`_of_tele_ext`) and transported endpoints — where
`#machine_endpoint` made `machine_ships_wired` (`generateCore`'s `wiredHead?`
table has all five heads [R 2604–2617]) and the `LeafKid` conditions are
decided. `toggleL.machine_leafKid` is BUILT (`NoPortsLoopParentTest`, in
AllTests). What is NOT known before the build: whether
`toggleL.machine_ships_wired` and `loopPair.machine_ships_wired` exist (the
wired form is generated inside a `try`; on failure only a progress line is
left) — the `LEAFENTRY DATA` line lists it, and row 6 is the refusal if not.

Memory and "transported" are therefore not separate scope tests: a memory is
a call entry (row 2); a transport changes nothing in the term.

## 4. The family (`Tests/Compiler/LeafEntryFamilyTest.lean`)

"endpoint — premise — predicted state", against each `f.machine_ships_wired`:

| endpoint | premise of `f.machine_ships_wired` | predicted state (pending build) |
|---|---|---|
| `cnt.machine_ships_leafC_regen` (compare path; `cnt.machine_ships_leafC` exists) | — | REBUILT, statement `isDefEq` the hand-built one [P]; nothing newly removed |
| `acc.machine_ships_leafC` | `simpleBody b = false` | absent [P] |
| | `seqCheck wof (weOf wof) (checkedOptimize b).body = true` | absent (discharged at `wofOf (checkedOptimize b)`) [P] |
| | the `declWidth` / `weOf` agreement on `seqNames` | absent [P] |
| | `MachineCloses acc` | absent (`acc.machine_closes`) [P] |
| | run, `MachineDefines acc` | stay, ALLOWED |
| | NEW `ChildBnd mref cref w` | ALLOWED |
| `pe.machine_ships_leafC` | the same four | the same [P] |
| `twoHW.machine_ships_leafC` | the same four | the same [P]; `twoHW.machine_leafKid` generated here (first time for this declaration) |
| `toggle.machine_ships_leafC` | the same four | the same [P]; `toggle.machine_leafKid` generated here |
| `loopPair.machine_ships_leafC` | the same four | the same [P], IF `loopPair.machine_ships_wired` exists (not known); `loopPair.machine_leafKid` generated here — a packed 64-bit tuple port |
| `toggleL.machine_ships_leafC` | the same four | the same [P], IF `toggleL.machine_ships_wired` exists (not known); `toggleL.machine_leafKid` imported (built) |

Shapes: `acc` — one 8-bit register, structure result with a `Bool` field;
`pe` — two 32-bit registers, a multiplication; `twoHW` — TWO registers of
different kinds (8-bit, `Bool`), shared `let`s; `toggle` — `Bool` register,
`Bool` OUTPUT, concrete domain; `loopPair` — `Signal.loop`, two WIDE (32-bit)
registers, tuple state as one port; `toggleL` — `Signal.loop`, `Bool`.
(32 bits is also the width at which the print guard can fall back —
`A-leaf-entry-2.md` §3.2; the theorem holds on either branch.)

REFUSED (expected class asserted): `pickByteH` (row 4), `parent` (row 3),
`memCounter` (row 2), `plain` (row 1). `toggleL` is NOT in this list: in
scope by §3.

Each generated endpoint is audited by `audit` (listing first, then: three
proposition binders, 0 NOT ALLOWED, the seven constants absent, the base
endpoint mentions the three checks and `MachineCloses`, standard axioms for
the endpoint, `machine_leafKid`, `machine_closes`).

SCOPE of every line above: one declaration as an entry, ONE module
(`MachineShips` at the emitter's own width map); not `DesignSV`, not the SV
string, not `#sim`; data conditions decided per declaration; the run, the
reflection, `ChildBnd` stay premises; a compiler with the two guards.

## 5. The census list, with PREDICTIONS by grep

Source: `A-census-2.md` §2.2 (the `#machine_endpoint` lines of the test
files, plus `ShippingMachineFuseTest`'s programmatic three). Kind by `grep`
of the definition for `circuit do` / `Signal.reg` / `runCircuitH` /
`Signal.loop` / `Signal.register` — NOT by the reader. **Every mark is a
prediction [P]**; "in" means "in the scope scan's scope IF
`machine_ships_wired` and `machine_closes` exist", not "GENERATED".

| file | declarations | kind by grep | predicted |
|---|---|---|---|
| (census first rows) | `cnt`, `acc`, `pe` | `circuit do` register | in (this round's test) |
| | `toggleL` | `Signal.loop` register | in (this round's test) |
| | `pickByteH` | combinational | REFUSED slotless (this round's test) |
| | `pick`, `pickD`, `rcH` | gate route | REFUSED not a machine |
| `ShippingMachineClosesTest` | `reflSharedLet`, `reflAliasLet`, `closesInputLet`, `closesOpAlias`, `closesChain` | `circuit do` register | in (5); `machine_closes` asserted present by that test [R 87] |
| `ShippingMachineCommandTest` | `mThree`, `twoHW`, `toggle`, `LINHW.checksumHW` | `circuit do` register | in (4; `twoHW`, `toggle` in this round's test) |
| | `twoFlag`, `twoCnt`, `linChk`, `linChkDefault` | a field of a `circuit do` structure result | in (4) |
| | `EcdsaSignDemo.wMulN`, `EcdsaSignDemo.wTx`, `P256SignDemo.wMul`, `P256SignDemo.wMulN`, `Fido2Demo.wTx` | `@[hardware_module]` wrappers of `circuit do` FSMs (256-bit / UART) | in (5); kernel cost of the `LeafKid` decides NOT known |
| `ShippingMachineLoopTest` | `wholeLoop`, `wholeToggle`, `counterLoop`, `accLoop`, `bottleneckController`, `dividerSignal`, `divQ`, `loopPair` | `Signal.loop` register | in (8; `loopPair` in this round's test) |
| `ShippingMachineNestTest` | `latch2`, `loopBack`, `front`, `pair`, `consumer` | nested sub-machines (register) | in (5), head `_of_nested` |
| `ShippingMachineNormTest` | `nConst`, `nLit`, `nMixed`, `nLift`, `nNot`, `nMapNot`, `nSlice` | `circuit do` register | in (7) |
| `ShippingMachineRawTest` | `counterH`, `twoCountH`, `mixedWidthH`, `tripleCountH`, `fourCountH` | `runCircuitH` register, NO input | in (5) |
| | `pairCounterCdo`, `tupReg` | `circuit do` register | in (2) |
| | `negSig`, `negLift`, `addThree`, `useHalf`, `triBundle`, `tupFst`, `tupMapFst`, `tupSum`, `tupHwLet3` | combinational | REFUSED slotless (9) |
| `ShippingMachineTeleTest` | `divInLoop`, `chain2`, `chain3` | telescope (register) | in (3), head `_of_tele_ext` |
| | `hftByte` | calls a `@[hardware_module]` byte table | REFUSED has calls |
| `ShippingMachineFuseTest` | `outer`, `siblings` | fused `Signal.loop` (register) | in (2); generated with `checkCloses := false` — `machine_closes` by `closesTheorem?` not known |
| | `withMemory` | memory | REFUSED memory |
| `ApplicativeSemanticsTest` | `reversed`, `reversedSurface`, `nestedSurface`, `constantRight`, `constantLeft`, `duplicate`, `withConstant`, `nested`, `complement`, `concatReverse`, `orderedLess`, `rightAssociated`, `permutedFour` | combinational | REFUSED slotless (13) |
| `ShippingMachineCombTest` | `pickByte`, `ipv4HeaderByte`, `ipv4HeaderChecksumSig`, `httpGetByte` | combinational | REFUSED slotless (4) |
| `ShippingSignOpsTest` | `sext`, `ashrK`, `shiftSurface`, `ashrSig`, `scaleMul`, `Requantize.requantize` | combinational | REFUSED slotless (6) |

Totals by this grep: 92 names; predicted in 54 (register: 7 of them run in
this round's test incl. `cnt`); REFUSED slotless 33; REFUSED calls / memory
2; REFUSED not a machine 3. The census's "about 80" was the count without
the first rows. So the generator's reach, if the predictions hold, is about
54 declarations, not 80: about a third of the leaf endpoints are slotless
(`machine_ships_comb`), which this round does not touch.

## 6. A sweep — NOT run, left to the integrator

`Tools.ShippingLeafEntryCommand.sweep (names : List Name)` logs, per name, the
`LEAFENTRY DATA` line and the outcome line, then one `LEAFENTRY SWEEP` line
with the four classes. It asserts nothing.

How: one target-only file (NOT in AllTests) importing the test files of §5
and `Tests.Compiler.LeafEntryFamilyTest`, with

    set_option maxHeartbeats 0 in
    run_cmd Tools.ShippingLeafEntryCommand.sweep [``…, …]

Importing the family test avoids a name clash on its seven declarations: the
sweep then takes the compare path on them (REBUILT), except `cnt`, whose
`_regen` exists (FAILED: "the compare path was run twice" — leave `cnt` out).
A sweep file and any later per-declaration test that generates the same
`machine_ships_leafC` / `machine_leafKid` must not both be in AllTests.

Cost per declaration (per-declaration kernel decides; none measured):

* `f.machine_leafKid`: six `decide`s on the data (`callsOk`, the late
  binders, the slot count, output widths / names / scalar types). For `cnt`,
  `acc`, `pe`, `toggleL` these are built, each inside a test that takes
  seconds [I]. For the 256-bit wrappers and `dividerSignal` not known.
* `f.machine_closes`: exists already wherever `#machine_endpoint` derived it.
* the endpoint: one application; the kernel compares the stored statement of
  `f.machine_ships_wired` with `leaf_entry_ships_of`'s hypothesis (the same
  text) — expected cheap [P].
* `collectAxioms` on three constants per declaration.

For the corpus (`scripts/shipping-coverage`, `machine_decls.txt`): a second
tail for `endpoints.sh` calling `sweep` on the machine-route declarations
after their `generate`; the list exists only as the output of a sweep I must
not run.

## 7. Integrator

`lakefile.lean`:

    lean_lib «Tools.ShippingLeafEntryCommand» where
      roots := #[`Tools.ShippingLeafEntryCommand]

`Tests/AllTests.lean`: `import Tests.Compiler.LeafEntryFamilyTest` (after
`Tests.Compiler.LeafEntryCntClosedTest`, which it imports).

Names added (environment): `machine_ships_leafC` under `acc`, `pe`, `twoHW`,
`toggle`, `loopPair`, `toggleL`; `cnt.machine_ships_leafC_regen`;
`machine_leafKid` under `twoHW`, `toggle`, `loopPair`. Clashes checked by
`grep`: no file defines any of these; `LeafEntryCntTest` adds
`cnt.machine_ships_leaf`, `…BndTest` adds `cnt.machine_ships_leafB`,
`…ClosedTest` adds `cnt.machine_ships_leafC` — none is redefined (the compare
path adds `_regen`). `machine_leafKid` of `cnt`, `acc`, `pe`, `toggleL` come
from `NoPortsTest`, `NoPortsTwoTest`, `NoPortsSlotlessEngineOnceTest`,
`NoPortsLoopParentTest` — IMPORTED by the family test, which is why it
imports them. Namespaces: `Tools.ShippingLeafEntryCommand`,
`Tests.Compiler.LeafEntryFamilyTest` (new). Syntax tokens:
`#machine_leaf_entry`, `#machine_leaf_entry_try` (no existing command starts
with `#machine_leaf`).

The files reference `leaf_entry_textChecks_closed` and `leaf_entry_ships_of`
only — not `mergeChecked_keeps_reg` / `_keeps_nonAssign`: they fit both
trees. (`LeafEntryCntClosedTest`, imported, does name the old one at lines
57 and 174 — the integrator's rename.)

Build order: `Tools.ShippingLeafEntryCommand`;
`Tests.Compiler.LeafEntryFamilyTest`; `Tests.AllTests`.

UNVERIFIED, highest risk first:

1. `loopPair` and `toggleL`: whether their `machine_ships_wired` exists (then
   row 6 REFUSED and the test's expected `GENERATED` fails at that line —
   change the expected class and report the refusal, or drop the line);
   `loopPair.machine_leafKid`'s decides on a packed tuple output;
2. `endpointTerm`: `forallTelescopeReducing` on `f.machine_ships_wired` giving
   exactly 11 binders (for a transported endpoint the stored type is that of
   an `Eq.mpr`); `mkAppM` of `leaf_entry_ships_of` unifying `?dom`, `?src`
   from the stored statement; `mkLambdaFVars` with `hbnd` (declared last)
   abstracted before `hr` and `entry`;
3. the compare path on `cnt`: `isDefEq` of the generator's statement with the
   hand-built one (same head, same arguments; the `Name` literal comes from
   `toExpr` there and from a quoted name here);
4. `twoHW` / `toggle` / `loopPair`: `leafKidTheorem` never ran on them (two
   output ports `cnt` / `flag`; a `Bool` port `out`), and that their
   `machine_closes` exists or is derived was not read (else REFUSED, row 7);
5. `scan`: `memCounter`'s memory as a call entry with `memChild? ≠ none`
   (otherwise it is refused by row 3 or 6 — still REFUSED, another reason);
   `plain` refused by `readMachine`;
6. `leafEntry`'s classification of a missing closing as REFUSED (by the
   message text) and the restore of the message log;
7. syntax: `structure` literals `{ data, refusal := … }` under `return`; long
   `s!` strings; `partial def soundHead`.

## Build record (integrator, 2026-10-13)

Built at the first attempt on poc 77b3ba4f (guards integrated) + this round's three files (worker files
unchanged); `LeafEntryFamilyTest` in AllTests. Tree `a3e219d05c5f73f2e740eea687299e1151675bca`.

Established by the command `#machine_leaf_entry` (no new theorem): for the leaf register machines `acc`,
`pe`, `twoHW` (two registers), `toggle` (Bool output), `loopPair` and `toggleL` (written as `Signal.loop`),
`f.machine_ships_leafC` has exactly three proposition binders — the run, `MachineDefines f`, `ChildBnd` —
0 NOT ALLOWED; against `f.machine_ships_wired` the premises `simpleBody b = false`, `seqCheck … (checkedOptimize
b).body`, the declWidth/weOf agreement and `MachineCloses f` are gone (`ChildBnd` is new); none of
`simpleBody` / `seqCheck` / `seqNames` / `MachineCloses` / `InvW` / `printOk` / `isAssign` occurs; standard
axioms. `cnt`: REBUILT, `isDefEq` the hand-built statement. REFUSED with reasons: `pickByteH` (slotless),
`parent` (has calls), `memCounter` (memory), `plain` (gate route).
Scope: one declaration each; a leaf register machine as an ENTRY; conclusion `MachineShips` of one module
(not `DesignSV`, not the SV string, not `#sim`); decided data conditions; runtime boundary. These rest on
the two compiler guards integrated in 50ffea04. The other ≈ 48 register leaves predicted in scope were not
run (no sweep).

```
20261013-152048-a32-tests: lake build Tools.ShippingLeafEntryCommand Tests.Compiler.LeafEntryFamilyTest 
result=success
exit=0
memory_peak_file=762998784
Build completed successfully (617 jobs).
20261013-152144-a32-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=432656384
Build completed successfully (1266 jobs).
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt: in the environment [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData, Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_sound, Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_cl
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc: in the environment [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_sound, Sparkle.Tests.Compiler.ShippingChildBoundaryTest.ac
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.MultiInstance.pe: in the environment [Sparkle.Tests.Compiler.MultiInstance.pe.machineData, Sparkle.Tests.Compiler.MultiInstance.pe.machine_sound, Sparkle.Tests.Compiler.MultiInstance.pe.machine_closes, Sparkle.Tests.Compiler.MultiInstan
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW: in the environment [Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW.machineData, Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW.machine_sound, Sparkle.Tests.Compiler.ShippingMachineEntryTest.
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle: in the environment [Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle.machineData, Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle.machine_sound, Sparkle.Tests.Compiler.ShippingMachineC
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair: in the environment [Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair.machineData, Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair.machine_sound, Sparkle.Tests.Compiler.ShippingMachineLoop
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL: in the environment [Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machineData, Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machine_sound, Sparkle.Tests.Compiler.ShippingMachi
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH: in the environment [Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH.machineData, Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH.machine_sound, Sparkle.Tests.Compiler.ShippingMa
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent: in the environment [Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machineData, Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_sound]
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: in the environment [Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machineData, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_sound]
an:98:0: LEAFFAMILY IMPORTS Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain: in the environment []
an:121:0: LEAFENTRY REBUILT Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt: REBUILT Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC: statement isDefEq the existing one (proof kept as Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC_regen). A
an:124:0: LEAFFAMILY COMPARE Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt: Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC_regen (the generator's term) against Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC (the hand-built term of LeafEn
an:124:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBody,
an:152:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBody,
an:159:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.MultiInstance.pe.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.MultiInstance.pe, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBody,
an:166:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBody,
an:173:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBo
an:180:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBody
an:187:0: LEAFENTRY AUDIT OK Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machine_ships_leafC: exactly three proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL, ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simple
an:192:0: LEAFENTRY REFUSED Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH: slotless: no register slot (LeafKid.slots asks shape.layout.slots ≠ []). Its ship-level endpoint is Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH.machine_ships_comb, which asks simpleBod
an:194:0: LEAFENTRY REFUSED Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent: has calls [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt, Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt] — a parent, not a leaf (LeafKid.leaf asks shape.insts = []). The generators for it: #machine
an:196:0: LEAFENTRY REFUSED Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: memory: call entries [SparkleMem.combo.4.8] are memories — a certified-route memory is an INSTANCE of a memory-only submodule, so Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter is
an:198:0: LEAFENTRY REFUSED Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain: not a machine declaration — the machine reader says: Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain: a combinational gate takes it, not the machine route. (A declaration the certified gate comp
an:200:0: LEAFFAMILY: REBUILT (isDefEq, proof kept as _regen) for cnt; GENERATED and audited [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_ships_leafC,
```
