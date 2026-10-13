# B-memgen: `#machine_no_ports_mem` — the memory-only endpoints by command (round par/b-20)

Status of everything below: **WRITTEN, NOT BUILT**. Nothing counts as removed until the integrator builds it.
No `lean` / `lake` / `iverilog` was started by the worker. Branch `par/b-20` from 950de375.

## 1. Files (all new)

| file | what |
|---|---|
| `Tools/ShippingNoPortsMemCommand.lean` | the command `#machine_no_ports_mem f` and `#machine_no_ports_mem_try f "EXPECTED"` |
| `Tests/Compiler/NoPortsMemGenFamilyTest.lean` | TARGET-ONLY: six generations, four refusals, goal gaps, audit |
| `Tests/Compiler/NoPortsMemGenCompareTest.lean` | the compare path on the hand test of `memCounter` |
| `docs/parallel/B-memgen.md` | this note |

No general theorem is added. The command lives under `Tools/` (not under `Tests/`): the meta helpers of
the hand libs are restated (§4).

## 2. The command and its scope

`#machine_no_ports_mem f` — an error where it is refused or fails.
`#machine_no_ports_mem_try f "EXPECTED"` — the outcome is logged
(`NOPORTS MEM f: GENERATED | REBUILT | REFUSED (reason) | FAILED (condition)`) and it is an error when its
class is not the expected one; a refused / failed declaration leaves nothing (environment and messages put back).

Scope: a machine with `machineData / machine_ok / machine_body / machine_sound / machine_composedT /
machine_ships_hier` (route `.mem`), at least one register slot, the general closing, EVERY call entry a
memory placeholder `SparkleMem.{combo|sync}.aw.dw` — either read kind, any number of different
placeholders, ONE `(aw, dw)` for all (the built `MemOnlyData d nDecl aw dw` takes one pair; the per-entry
generalisation is NOT written, a width difference is refused). Transported endpoints are covered
(`composedG_src`). Depth 0, at-form closing (`MachineClosesAt`) only.

Generated, in this order (lemmas under `f.noPortsMem_*`; the two endpoints under the hand tests' names):

    f.noPortsMem_entry                                   every entry is one of the placeholders (decided)
    f.noPortsMem_calls / _slots / _domB / _outTy / _callWidths / _callArgs / _outChars / _outScalar   (decided)
    f.noPortsMem_data            : MemOnlyData f.machineData nDecl aw dw
    f.noPortsMem_runFacts / _outsG0 / _kidsMemG / _designP0          memOnly_* at f's data
    f.machine_design_noPortsR0                           head machine_design_noPorts at n = 0
    f.noPortsMem_alias / _argsN / _field / _argsNd / _outHead        (decided)
    f.noPortsMem_closeData       : MemOnlyCloseData f.machineData
    f.noPortsMem_notin{j}        f does not print as placeholder j's module name
    [≥ 2 placeholders: f.noPortsMem_at{j}, f.noPortsMem_namesNe{i}_{j} (i < j), f.noPortsMem_sep, f.noPortsMem_parent]
    f.noPortsMem_closes          : MachineClosesAt f — NO premise   (the "f_closes" of the hand tests)
    f.machine_design_noPortsR0_closed

then the premise lines of both endpoints (`NOPORTS MEM PREMISE …`), with the command's own assertions:
exactly one NOT ALLOWED in the open endpoint, none in the closed one, one line fewer; `f.noPortsMem_closes`
has no proposition premise; neither statement mentions a checker constant, the closed one no
`MachineClosesAt` / `MachineCloses` / `ChildRanIn`; a transported statement does not read the rewritten source.

NAMES: the hand lemmas are in their test's namespace (`Tests.Compiler.NoPortsMemOnlyCounterTest.memCounter_data`,
…), so "the same names" holds for the two ENDPOINTS only; the lemmas are `f.noPortsMem_*` and never clash
with the hand ones. `…_closed_gap` is NOT made by the command (`#machine_goal_gap_of`, as in the hand tests).

Compare path (never a silent return): for EVERY name the command would add, if it exists the theorem is
rebuilt, added as `…_regen` (kernel-checked) and its statement must be `isDefEq` the existing one — an
error otherwise. Lemmas: by elaborating the same text under the `_regen` name; endpoints: the built
`Tools.ShippingNoPortsKidsCommand.addOrCompare`.

## 3. Refusal table

| condition (in the order tested) | class | reason line (abridged) |
|---|---|---|
| no `f.machineData / machine_ok / machine_body` | REFUSED | not a machine with an endpoint |
| no call entry | REFUSED | no call |
| a non-memory callee that is, or reaches (≤ 8 levels of machine callees), a machine with a memory child | REFUSED | memory at depth ≥ 1: not covered |
| no memory callee | REFUSED | no memory callee (machine / gate children: other commands) |
| memory entries and other callees | REFUSED | mixed memory / machine children: the seqMem pattern, not generated here |
| no register slot | REFUSED | parent without a register |
| `instFields = []` | REFUSED | not the general closing |
| placeholders of different `(aw, dw)` | REFUSED | entries with different widths: not covered |
| an entry without 4 argument lets | REFUSED | `hargsN` is false |
| `instFields` shorter than the entries, or a field not `out` | REFUSED | `hfield` is false |
| two entries of one placeholder on one argument list | REFUSED | one memory read twice on the same argument lets (`hargsNd` is false) |
| an output name starting with `i` | REFUSED | `hout` is false |
| no `machine_sound / machine_composedT / machine_ships_hier` | REFUSED | run `#machine_composedT`, `#machine_ships_hier` first |
| `machine_ships_hier` not of the memory route (reset not `ResetM`, bound not `kidsMem`, boundary not `True`, closing not `MachineCloses`, 24 arguments / 11 binders) | FAILED | the line of `endpointTerm` |
| a decided data condition is false (`callsOk`, `callWidthsOk`, `callArgsOk`, `letsAliasOk`, …) | FAILED | `<name>: the generated proof fails: …` |
| an existing name with another statement | FAILED | EXISTS with a different statement |

All-worlds endpoints: `f.machine_design_noPorts0` (closing premise `MachineCloses`) is NEVER generated;
the log line of every generation says so (`MachineCloses` cannot be discharged for a shape with calls,
`Tools/ShippingMemOnlyAtAll.lean`). The exchange endpoint of `NoPortsMemOnlyCounterTest` stays hand-only.

`seqMem` (leaf register child + memory placeholder): NOT WRITTEN. Its hand pattern is two files of 567 +
606 lines over another interface (`KidFactsM` per entry, `machineClosesAt_of_kidsDM` with a real child's
reflection, a boundary with `MachineDefines cnt`) — not a small extension of this command. No
`#machine_no_ports_memseq`.

## 4. Restated vs imported

Imported (BUILT): `Tools.ShippingNoPortsKidsCommand.{dischargeWith, closedTerm, addOrCompare, regenName}`,
`Tools.ShippingShipsFreeCommand.checkMade`, `Tools.ShippingMachineSeqCommand.endpointParts`,
`Tools.ShippingMachineLinkedCommand.addTheorem` (through `addOrCompare`), `Tools.ShippingFinalGoalCommand.{allowed, isPropArrow}`.

Restated from `Tests/` (a `Tools/` file cannot import them) — about 182 lines of meta code:

| restated as | from | lines |
|---|---|---|
| `forbiddenMem` | `Tests/Compiler/NoPortsMemOnlyCounterTest.lean` 149–152 | 4 |
| `finish0` | `finishM0`, same file 162–205 (the `Tests` `dischargeWith` replaced by the built `Tools` one, same body) | 44 |
| `endpointTerm` | `generateT0`, `Tests/Compiler/NoPortsMemWithMemoryLib.lean` 141–227; returns statement and proof instead of adding them; one more refusal (the statement must not mention `MachineCloses`) | 87 |
| `innerAntecedents`, `premiseLines` | `Tests/Compiler/NoPortsTest.lean` 114–160, prefix `NOPORTS MEM PREMISE` | 47 |

`closeLast` (`NoPortsMemSeqMemClosedTest` 421–446) is NOT restated: the built `closedTerm … 0` is the same
construction (last binder `MachineClosesAt f` replaced by the closing theorem's premises — none here).

The theorem texts are the hand files' theorems as syntax quotations: single placeholder —
`NoPortsMemOnlyCounterTest` 402–563 and `NoPortsMemOnlyClosedMemCounterTest` 76–135; several placeholders —
`NoPortsMemOnlyAtMixedMemsTest` (entry as a disjunction, `mem` by `Or.elim`) and
`NoPortsMemOnlyClosedMixedMemsTest` 75–198 (`at`, `names_ne`, `sep`, `parent`). DIFFERENCES from the hand
texts (each is a place where the build may disagree):

* `mem_isMem` is inline (`show memChild? … = some … from by first | rfl | decide`), not a named theorem;
* the two-way `rcases` of `mixedMems_sep` / `_parent` is written as nested `Or.elim` terms after `intro`
  (any number of placeholders; only two are exercised);
* single placeholder: the `mem` field is `have h := entry k hk; Exists.intro cb (…)` where the hand has
  `Exists.intro true ((congrArg memChild? (entry k hk)).trans mem_isMem)`;
* every generated theorem is under `set_option maxHeartbeats 4000000` (the hand data lemmas use the default).

## 5. Family: endpoint — premise — predicted state

Nothing new is removed for any declaration: the same statements as the BUILT hand tests, by command.

| endpoint | premise | predicted state |
|---|---|---|
| `memCounter / syncNarrow / memWide / twoMems / mixedMems .machine_design_noPortsR0` | `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0` (of `f.machine_design_sv0`) | predicted absent, as in the hand endpoint — WRITTEN, NOT BUILT |
| | boundary `True` | `ChildBnd mref cref w` (ADDED, allowed) |
| | `MachineCloses f` | `MachineClosesAt f` — still a premise, the one NOT ALLOWED |
| | the run, `MachineDefines f` | stay |
| the same five `…_closed` | `MachineClosesAt f` | predicted absent (`f.noPortsMem_closes`, no premise); 0 NOT ALLOWED |
| `withMemory.machine_design_noPortsR0` | `shipsHierCheck`, `kidsMem` (of `withMemory.machine_ships_hier`; no design-level base) | predicted absent |
| | boundary `True`; `MachineCloses` | `ChildBnd` (ADDED); `MachineClosesAt` (NOT ALLOWED) |
| `withMemory.machine_design_noPortsR0_closed` | `MachineClosesAt withMemory` | predicted absent; 0 NOT ALLOWED; reads `machineSourceDecl` |
| `…_closed_gap` (six, by `#machine_goal_gap_of` in the test) | gap hypotheses | predicted none |
| `seqMem` | — | REFUSED: mixed memory / machine children |
| `cnt` | — | REFUSED: no call |
| `parent` | — | REFUSED: no memory callee |
| `midH` | — | REFUSED: no memory callee (its callee is the gate child `rcH`) |
| compare test: `memCounter.machine_design_noPortsR0[_closed]` | all | UNCHANGED; rebuilt statements `isDefEq`, kept as `…_regen` |

COUNT: the task text says "all six memory-only declarations and `withMemory`". There are five untransported
memory-only parents with a hand endpoint plus `withMemory` = six memory-only declarations; the seventh
memory declaration is `seqMem`, refused here. The family test generates six.

## 6. Further declarations the command would cover, without a test

Searched: every `.lean` file that mentions `Signal.memory` / `memoryComboRead` AND contains
`#machine_endpoint` or `ShippingMachineCommand.generate`.

With an endpoint in the repository — ALL are already in the family test or refused:

| declaration | file:line | state |
|---|---|---|
| `memCounter`, `twoMems`, `mixedMems` | `Tests/Compiler/ShippingMachineMemLinkedTest.lean`:17, 27, 38 | in the family test |
| `memWide`, `syncNarrow` | `Tests/Compiler/ShippingDesignSVMemTest.lean`:23, 33 | in the family test |
| `withMemory` | `Tests/Compiler/ShippingMachineFuseTest.lean`:42 | in the family test |
| `seqMem` | `Tests/Compiler/ShippingChildBoundaryTest.lean`:52 | refused (mixed) |

So there is NO further declaration with a `#machine_endpoint` in the repository that the command would cover.

Memory users WITHOUT any `#machine_endpoint` / `#machine_composedT` / `#machine_ships_hier` in the
repository (candidates only after those three commands are run on them; whether they are memory-only
parents with a register was NOT read off the reader — nothing was run):

| declaration at | read |
|---|---|
| `Tests/Synthesis/SynthCatalog.lean`:285 (catalogue entry 23, "Signal.loop + memoryComboRead") | a loop with a combinational-read memory: the `memCounter` shape by its comment — likeliest candidate |
| `Sparkle/Library/Queue/SyncFIFO.lean`:85 | `memoryComboRead` inside the FIFO's state; other callees not checked |
| `Examples/SimpleMemory.lean`:29, 84; `Examples/MemorySynthesis.lean`:29 | a bare `Signal.memory` (line 84: over registered operands); a declaration that is ONE memory has no register slot and would be refused ("parent without a register") if it is on the machine route at all |
| `Tests/Compiler/ShippingMemorySoundnessTest.lean`:24, 91 | bare memories of the S5 layer (not the machine route's endpoints) |

No tests were written for them.

## 7. For the integrator

- `lakefile.lean`: `lean_lib «Tools.ShippingNoPortsMemCommand» where` / `  roots := #[`Tools.ShippingNoPortsMemCommand]`.
- `Tests/AllTests.lean`: NO import for `NoPortsMemGenFamilyTest` (target-only). `NoPortsMemGenCompareTest`
  MAY be imported (it adds only new names: `memCounter.noPortsMem_*`, `…_noPortsR0_regen`,
  `…_noPortsR0_closed_regen`); not required.
- Name clashes: `NoPortsMemGenFamilyTest` creates `f.machine_design_noPortsR0[_closed[_gap]]` for the six
  declarations — a duplicate declaration with `NoPortsMemOnlyAt<Decl>Test`, `NoPortsMemOnlyClosed<Decl>Test`,
  `NoPortsMemOnlyAtProbe`, `NoPortsMemWithMemoryTest`, and with `NoPortsMemGenCompareTest` (which imports a
  hand test). Never co-import. `f.noPortsMem_*`: grep finds no other user of the prefix.
- Build order: `Tools.ShippingNoPortsMemCommand` → `Tests.Compiler.NoPortsMemGenCompareTest` (small: one
  declaration, hand test already built) → `Tests.Compiler.NoPortsMemGenFamilyTest`.

## 8. What may not elaborate, most likely first

1. Syntax-quotation details of `Tools/ShippingNoPortsMemCommand.lean` (unbuilt meta code): the term
   `(have $h := $e; $b)` in `orElim`; the binder splice `$tail*` after literal binders in `runTheorem`
   (the built kids command has this shape with `$bs*`); `theorem $tn …` with `tn` passed through a
   closure; `let mut sepT : Term ← …`.
2. The several-placeholder path (`mixedMems` only): `Or.elim` terms instead of the hand `rcases`
   (`(entry k hk).elim (fun h => …) (fun h => …)` under `exact`), and `namesNe0_1` / `at{j}` as generated.
3. `emit`'s compare of lemma statements, and macro-scoped binder names in the generated signatures
   (the hand theorems have plain names; the generator applies them positionally with `mkAppM`, so names
   should not matter).
4. `endpointTerm` on an untransported parent: restated from `generateT0`, which was built on `withMemory`
   only ("for an untransported parent it builds what `generateM0 (atForm := true)` builds" was never run).
   The compare test decides it for `memCounter` (`isDefEq` with the `generateM0` statement).
5. `closedTerm … 0` in place of the hand `closeLast` (same construction by reading; `closedTerm` was built
   with trailing reflections ≥ 0 — whether it ran with 0 before is not known to the worker).
6. Heartbeats / recursion depth: the command sets `maxRecDepth 1000000` and `maxHeartbeats 0` in the
   `Core.Context` of its two `MetaM` parts and the tests wrap it in `set_option maxHeartbeats 0`; the
   elaborated theorems carry `maxHeartbeats 4000000`.
7. Audit assertions of the family test that go beyond the hand audits: none known; the transported /
   untransported `machineSourceDecl` presence is asserted for `withMemory` only and LOGGED for the others.
8. Refusal reasons: `midH` may be refused by the first test ("not a machine with an endpoint") or by "no
   memory callee" — either is class REFUSED; the log says which.

## 9. Not covered

Depth ≥ 1; per-entry widths; mixed memory / machine children (`seqMem`); slotless memory parents;
the all-worlds endpoint; `…_closed_gap` by the command itself; the isDefEq of the generated statements
with the hand ones for the five declarations other than `memCounter` (the family test's closure has no
hand test; add one compare file per declaration if wanted — each is the 60 lines of
`NoPortsMemGenCompareTest` with another name).

## Build record (integrator, 2026-10-13)

Built at the first attempt on poc 950de375 + this round's files (worker files unchanged).
`NoPortsMemGenCompareTest` is in AllTests; `NoPortsMemGenFamilyTest` is target-only (it creates the names
owned by the hand tests). No premise is removed by this commit: the command `#machine_no_ports_mem`
produces, for memory-only parents (one `(aw, dw)`, either read kind, transported or not), the SAME
statements the hand tests have — compare path on `memCounter`: REBUILT, `isDefEq`, `_regen` kept; family
(separate closure): `memCounter`, `syncNarrow`, `memWide`, `twoMems`, `mixedMems`, `withMemory` GENERATED
and audited (0 NOT ALLOWED on `_closed`, no checker constant, standard axioms); `seqMem`, `cnt`, `parent`,
`midH` REFUSED with reasons. Not written: differing widths, the seqMem pattern, memory at depth ≥ 1.

```
20261013-115406-b20-tests: lake build Tools.ShippingNoPortsMemCommand Tests.Compiler.NoPortsMemGenCompareTest Tests.Compiler.NoPortsMemGenFamilyTest 
result=success
exit=0
memory_peak_file=1012551680
Build completed successfully (595 jobs).
20261013-115505-b20-alltests: lake build Tests.AllTests Tests.Compiler.NoPortsMemGenFamilyTest 
result=success
exit=0
memory_peak_file=639614976
Build completed successfully (1251 jobs).
st.lean:43:0: NOPORTS MEM GEN COMPARE Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: the command REBUILT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0 and Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0_closed from the reader's data; both rebuilt statements are isDefEq the hand ones (kept as …_regen, standard axioms)
t.lean:98:0: NOPORTS MEM Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem: REFUSED (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem: mixed memory / machine children (memory entries [SparkleMem.combo.4.8], other callees [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt]): the seqMem pattern, not generated here)
t.lean:101:0: NOPORTS MEM Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt: REFUSED (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt: no call (no instance statement: there is no child to derive facts about))
t.lean:104:0: NOPORTS MEM Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent: REFUSED (Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent: no memory callee (its callees [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt] are machine / gate children: #machine_no_ports, #machine_no_ports_kids, #machine_oneout_any are the commands for them))
t.lean:107:0: NOPORTS MEM Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH: REFUSED (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH: no memory callee (its callees [Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH] are machine / gate children: #machine_no_ports, #machine_no_ports_kids, #machine_oneout_any are the commands for them))
t.lean:317:0: NOPORTS MEM GEN AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: GENERATED by #machine_no_ports_mem (1 distinct placeholder(s), not transported); Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest
t.lean:317:0: NOPORTS MEM GEN AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow: GENERATED by #machine_no_ports_mem (1 distinct placeholder(s), not transported); Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPortsR0, Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.ShippingDesignSVMemTest.syncNarrow.machine_
t.lean:317:0: NOPORTS MEM GEN AUDIT Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide: GENERATED by #machine_no_ports_mem (1 distinct placeholder(s), not transported); Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0, Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPor
t.lean:317:0: NOPORTS MEM GEN AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems: GENERATED by #machine_no_ports_mem (1 distinct placeholder(s), not transported); Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.
t.lean:317:0: NOPORTS MEM GEN AUDIT Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems: GENERATED by #machine_no_ports_mem (2 distinct placeholder(s), not transported); Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mi
t.lean:317:0: NOPORTS MEM GEN AUDIT Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory: GENERATED by #machine_no_ports_mem (1 distinct placeholder(s), transported); Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0, Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed, Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_desi
t.lean:334:0: NOPORTS MEM GEN FAMILY: GENERATED (six): memCounter, syncNarrow, memWide, twoMems (one placeholder each; twoMems two entries of it), mixedMems (two placeholders: both read kinds), withMemory (transported). REFUSED with reasons (logged above), nothing added: [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem,
```
