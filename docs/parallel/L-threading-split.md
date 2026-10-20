# The threading theorems over `MachineRan`, split IN PLACE; the copies removed

Branch `fix/ran-threading-split` (base poc `80745d94`; independent of `fix/projchain-total`).
**WRITTEN, NOT BUILT.** Nothing here was compiled or run by Lean. What IS checked is what a
script can check on text (below, marked SCRIPT). "BUILT" / "MEASURED" appear only for what the
integrator's record in `docs/parallel/G-mixdeep-outermost.md` states.

Ruling implemented (reviewer, 2026-10-14, second message, item 4): "threading の 5 箇所 in-place
split 可。従来文を系として保持し型照合、コピー削減を別 commit に。" — the theorems that only
THREAD the closing may be split in place; the old statement stays as a corollary and is
type-checked; the removal of the copies is its own commit.

No file under `Sparkle/`, not `lakefile.lean`, not `Tests/AllTests.lean`. No `sorry`, no axiom, no
`native_decide`. No statement of an existing theorem changes.

## 0. Result, plainly

| | state |
|---|---|
| threading theorems split in place | **17 of 17** (every `_ran` sibling the two copy files held), in **9** built files |
| old statements | character for character the base commit's — SCRIPT (SHA-256 of both texts, `IDENTICAL` for all 17) |
| the `_ran` forms | the SAME full names the copy files declared; statement and proof are, character for character, the copy's text at the base commit (which the integrator BUILT); and — up to white space — the old statement / proof with the run binders removed, `closes ↦ ran`, callees `↦ _ran` — SCRIPT, both |
| duplicated proof lines | 0 (≈ 260 before) |
| the two copy files | import-only: they declare nothing |
| importers edited | none |
| theorems I could not split | none |

**One deviation from the task text, and why.** The task names FIVE built files
(`ShippingChecksCoreGate`, `ShippingChecksRunFacts`, `ShippingTextShipped`, `ShippingKidFacts`,
`ShippingMachineSeqLinkedR`) with 10 of the 17 theorems. The other 7 copies are of theorems in
four files the first split already edited (`ShippingChecksWidths`: `core_callPorts`,
`core_instOutWidthsOk`, `core_hierGate`; `ShippingChecksRaw`: `core_raw_facts`;
`ShippingPortsMatchRaw`: `core_portsMatch_raw`; `ShippingKidsSelf`: `core_kidsPass_deep`,
`core_kidsMaskedN_top`) — `G-mixdeep-outermost.md` §2.4 says so: "five [more built files] and
more theorems in the ten already edited". They cannot be left as copies: the copy file sits ABOVE
`ShippingKidFacts` in the import order, and `core_runFacts_ran` (to be in `ShippingChecksRunFacts`)
calls `core_raw_facts_ran`, `core_hierGate_ran`, `core_instOutWidthsOk_ran`; `kids_designCheck_ran`
calls `core_portsMatch_raw_ran`, `core_kidsPass_deep_ran`; and so on. So the in-place split is of
all 17, in 9 files; one commit per file.

## 1. The form (the first split's, unchanged)

For a theorem `X` with statement `S` and proof `P` that passes `hB hcore hpost entry closes` on:

    theorem X_ran  <S without {w w1}, hB, hcore, entry; closes ↦ (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)> :=
      P'                                   -- P with every call  Y … hB hcore hpost entry closes …  ↦  Y_ran … hpost ran …
    theorem X  <S, character for character> :=
      X_ran <the explicit binders of the _ran form, in order>
        (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes) <the explicit binders after it>

The three wired heads have `hr entry closes hsyn` instead (their `{w w'}`); the producer is
`machineRan_of_closes hr entry hsyn closes`, the `ran` binder
`(ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref declName d.shape m design)`.

`X_ran` sits immediately BEFORE `X`, in `X`'s namespace, under `X`'s `open` list and section
variables. Its doc comment is new (it said "COPIED … does not follow"); `X` keeps its doc comment
and its `set_option maxHeartbeats … in` line. `X_ran` has the `set_option` line the copy had.

## 2. How it was produced — `scripts/ran_threading_split.py`

Never by hand. `apply N` does one file:

1. finds the block of `<name>_ran` in the copy file and the block of `<name>` in the built file
   (each `theorem <name> ` must occur exactly once — asserted);
2. ASSERTS, before anything moves, that the copy IS the original in the split's form:
   * statement: the original's, white space normalised, with each run binder removed (each must
     occur exactly once) and the closing binder replaced by the `ran` binder, equals the copy's;
   * proof: the original's with the identifiers `hB`, `hcore`, `entry` (`hr`, `entry`, `hsyn`)
     dropped, `closes ↦ ran`, every name of the chain `↦ <name>_ran`, equals the copy's up to
     white space; the number of renamed callees equals the number of uses of `closes`; the copy's
     proof mentions none of the dropped identifiers;
3. replaces the original's block (asserted to occur once) by `X_ran` (the copy's statement and
   proof VERBATIM, the line layout the integrator built) followed by `X` with the corollary;
   re-reads the file and asserts `X`'s statement text is unchanged;
4. deletes the copy's block from the copy file;
5. adds `import Tools.ShippingMachineRanBase` where the file did not have it; for the heads, adds
   `machine_trace_lets_of_streamBRA_ran` to the file's `open Tools.ShippingMachineTraceX (…)`.

`verify` (run after all steps; output in §4) re-extracts every old statement from
`git show 80745d94:<file>` and from the tree and compares the texts and their SHA-256; compares
every `_ran` statement and proof with the copy file's text at the base commit; asserts each `_ran`
name is declared in exactly one file under `Tools/`, its original's; and asserts no import cycle.

Why the copy's text and not a fresh transformation: the copy was BUILT (G's record: "the threading
siblings", first attempt). Step 2 shows it is the original's proof with the callees swapped, so
"the proof moved" is literally true, and what is now in the built file is a text Lean has accepted
— in a file with MORE imports; at its new position it sees exactly what the ORIGINAL proof saw,
and the original was built there.

## 3. Commits, in order, and why every commit is a consistent tree

| # | SHA | files | content |
|---|---|---|---|
| 0 | `bb95e713` | `scripts/ran_threading_split.py` | the script; nothing applied |
| 1 | `2fa0cd12` | `Tools/ShippingChecksCoreGate.lean`, `Tools/ShippingKidFactsRan.lean` | `core_outsCheck_all_gate` |
| 2 | `58fa2fdc` | `Tools/ShippingChecksWidths.lean`, copy file | `core_callPorts`, `core_instOutWidthsOk`, `core_hierGate` |
| 3 | `bdcb0c75` | `Tools/ShippingChecksRaw.lean`, copy file | `core_raw_facts` |
| 4 | `58358381` | `Tools/ShippingPortsMatchRaw.lean`, copy file | `core_portsMatch_raw` |
| 5 | `14a53d04` | `Tools/ShippingKidsSelf.lean`, copy file | `core_kidsPass_deep`, `core_kidsMaskedN_top` |
| 6 | `1d3d91b4` | `Tools/ShippingChecksRunFacts.lean`, copy file | `core_runFacts` |
| 7 | `c1f577e4` | `Tools/ShippingTextShipped.lean`, copy file | `core_designCheck_run` |
| 8 | `a3d81508` | `Tools/ShippingKidFacts.lean`, copy file | `kids_runFacts`, `kids_outsCheck`, `kids_maskedN`, `kids_designCheck` |
| 9 | `9ef26e8d` | `Tools/ShippingMachineSeqLinkedR.lean`, `Tools/ShippingMachineSeqLinkedRan.lean` | the three wired heads |
| 10 | `9bb840e4` | the two copy files | import-only stubs (the empty namespace skeletons removed, headers rewritten) |
| 11 | (next) | `Tests/Compiler/RanThreadingStatementsTest.lean`, the script (`record` mode), this record, `L-threading-split-statements.md` | the pin test and the records |

**"コピー削減を別 commit に" — what is and what is not separate.** A `_ran` form introduced in a
built file has the SAME full name as its copy, and the copy file imports the built file: the two
cannot coexist in one tree. So in commits 1–9 each copy's DELETION rides with the commit that
introduces the in-place form — a pure deletion hunk in the copy file, nothing else touched there.
The alternative that keeps commits 1–9 free of the copy files is to rename the 17 copies first
(`…_ranCopy`), re-point `Tools/ShippingOutermostCommand.lean` and the pin test at the temporary
names, and re-point them back at the end: three edits of built consumers to move text that the
script already proves identical (§2, step 2). Not done; it is the worse diff to review. What IS
its own commit (10) is the reduction of the two copy FILES to import-only stubs.

Consistency of each intermediate tree (by READING the import lines and the call sites; SCRIPT for
the single-declaration and cycle checks at the end):

* a `_ran` form is declared exactly once at every commit (moved, never duplicated);
* the order follows the import order, so every `_ran` callee of a moved proof is already in a
  file the new home imports: 1 needs only base forms (`core_kids_facts_ran`); 2 needs
  `core_callPortsM_ran`, `core_hierGateM_ran` (same file); 3 `core_raw_factsM_ran` (same file);
  4 `core_closed_typedIn_ran`, `core_callConns_ran`; 5 `core_kids_facts_ran`,
  `core_kids_self_ran`, `core_callConns_ran` and `core_hierGate_ran` (commit 2); 6
  `core_raw_facts_ran` (3), `core_hierGate_ran`, `core_instOutWidthsOk_ran` (2),
  `core_linkedWF_ran`, `core_outsExtracted_ran`; 7 `core_runFacts_ran` (6),
  `core_closed_typedIn_ran`; 8 the forms of 1, 2, 4, 5, 6, 7 and `core_clk_ran`; 9
  `machine_trace_lets_of_streamBRA_ran`. Each original already calls the non-`_ran` callee from
  the same file, so the import exists;
* the copies still in the copy file after a commit call moved forms by FULL name, and the copy
  file imports `Tools.ShippingKidFacts` (everything): they resolve;
* the consumers (`Tools/ShippingOutermostCommand.lean`, `Tests/Compiler/RanSplitStatementsTest.lean`)
  import the copy files, which import the built files: every `_ran` name resolves at every commit.

### The copy files after commit 10

`Tools/ShippingKidFactsRan.lean`: `import Tools.ShippingKidFacts`, `import
Tools.ShippingMachineRanBase` (its imports before) and a header saying where each form is.
`Tools/ShippingMachineSeqLinkedRan.lean`: `import Tools.ShippingMachineSeqLinkedR` and a header.
NOTHING is declared in either. Kept, not deleted, because `lakefile.lean` (not to be edited here)
names both as `lean_lib` roots (lines 2828–2832) and two files import them. To delete them later:
remove the two `lean_lib` entries, and replace the import lines in
`Tools/ShippingOutermostCommand.lean` (2–3) and `Tests/Compiler/RanSplitStatementsTest.lean` (2–3)
by `import Tools.ShippingKidFacts` / `import Tools.ShippingMachineSeqLinkedR`.

## 4. Per file (`git diff --numstat 80745d94`) and the statement table

| built file | +/− | import added | what |
|---|---|---|---|
| `Tools/ShippingChecksCoreGate.lean` | +46 −11 | `import Tools.ShippingMachineRanBase` | 1 theorem split |
| `Tools/ShippingChecksWidths.lean` | +125 −24 | — (had it) | 3 |
| `Tools/ShippingChecksRaw.lean` | +33 −3 | — (had it) | 1 |
| `Tools/ShippingPortsMatchRaw.lean` | +62 −11 | — (had it) | 1 |
| `Tools/ShippingKidsSelf.lean` | +89 −23 | — (had it) | 2 |
| `Tools/ShippingChecksRunFacts.lean` | +53 −16 | `import Tools.ShippingMachineRanBase` | 1 |
| `Tools/ShippingTextShipped.lean` | +51 −6 | `import Tools.ShippingMachineRanBase` | 1 |
| `Tools/ShippingKidFacts.lean` | +156 −32 | `import Tools.ShippingMachineRanBase` | 4 |
| `Tools/ShippingMachineSeqLinkedR.lean` | +220 −29 | `import Tools.ShippingMachineRanBase`; `open Tools.ShippingMachineTraceX (… machine_trace_lets_of_streamBRA_ran)` | 3 |
| `Tools/ShippingKidFactsRan.lean` | +14 −826 | — | import-only |
| `Tools/ShippingMachineSeqLinkedRan.lean` | +16 −271 | — | import-only |

The added lines in the built files are the re-stated OLD statements (the corollaries) and six
lines of doc comment per `_ran` form; the proof text moved. Net over `Tools/`: +865 −1252.

Imports: the five files get the line explicitly (each would have it transitively through
`ShippingChecksCore` / `ShippingMachineTraceX`; explicit so that a file names its own dependency,
as in the first split). No cycle — SCRIPT: the import closure of `Tools.ShippingMachineRanBase`
(135 modules, computed over the `import` lines) contains none of the nine edited files.

Statements (SCRIPT, `verify` / `table`; the full texts, old and `_ran`, with full digests, are in
`docs/parallel/L-threading-split-statements.md`, generated by `record`):

| theorem | file | old statement: sha256 at `80745d94` = now | binders (old → `_ran`) | proof lines moved | old proof now |
|---|---|---|---|---|---|
| `Tools.ShippingChecksCoreGate.core_outsCheck_all_gate` | `Tools/ShippingChecksCoreGate.lean` | `4b20a5852e8136b6` = `4b20a5852e8136b6` IDENTICAL | 25 → 20 | 23 | 2 lines |
| `Tools.ShippingChecksWidths.core_callPorts` | `Tools/ShippingChecksWidths.lean` | `831fd1af686804d0` = `831fd1af686804d0` IDENTICAL | 23 → 18 | 9 | 2 lines |
| `Tools.ShippingChecksWidths.core_instOutWidthsOk` | `Tools/ShippingChecksWidths.lean` | `7bac90d6cf5517b5` = `7bac90d6cf5517b5` IDENTICAL | 24 → 19 | 18 | 2 lines |
| `Tools.ShippingChecksWidths.core_hierGate` | `Tools/ShippingChecksWidths.lean` | `f12d2fbf25e3a5c8` = `f12d2fbf25e3a5c8` IDENTICAL | 22 → 17 | 2 | 2 lines |
| `Tools.ShippingChecksRaw.core_raw_facts` | `Tools/ShippingChecksRaw.lean` | `d3c1d066248c326b` = `d3c1d066248c326b` IDENTICAL | 23 → 18 | 2 | 2 lines |
| `Tools.ShippingPortsMatchRaw.core_portsMatch_raw` | `Tools/ShippingPortsMatchRaw.lean` | `701f9e3e03788afa` = `701f9e3e03788afa` IDENTICAL | 31 → 26 | 56 | 3 lines |
| `Tools.ShippingKidsSelf.core_kidsPass_deep` | `Tools/ShippingKidsSelf.lean` | `7b2a796c4e970eac` = `7b2a796c4e970eac` IDENTICAL | 24 → 19 | 27 | 2 lines |
| `Tools.ShippingKidsSelf.core_kidsMaskedN_top` | `Tools/ShippingKidsSelf.lean` | `bdc9ee42dcf8370d` = `bdc9ee42dcf8370d` IDENTICAL | 23 → 18 | 7 | 2 lines |
| `Tools.ShippingChecksRunFacts.core_runFacts` | `Tools/ShippingChecksRunFacts.lean` | `fc4d2744a28d92cb` = `fc4d2744a28d92cb` IDENTICAL | 25 → 20 | 15 | 2 lines |
| `Tools.ShippingTextShipped.core_designCheck_run` | `Tools/ShippingTextShipped.lean` | `111869251b964a9e` = `111869251b964a9e` IDENTICAL | 30 → 25 | 6 | 2 lines |
| `Tools.ShippingKidFacts.kids_runFacts` | `Tools/ShippingKidFacts.lean` | `ea9bee80ebb7a86c` = `ea9bee80ebb7a86c` IDENTICAL | 28 → 23 | 5 | 2 lines |
| `Tools.ShippingKidFacts.kids_outsCheck` | `Tools/ShippingKidFacts.lean` | `015b2adad5281d50` = `015b2adad5281d50` IDENTICAL | 26 → 21 | 5 | 2 lines |
| `Tools.ShippingKidFacts.kids_maskedN` | `Tools/ShippingKidFacts.lean` | `7eb3d9e0e23c41a3` = `7eb3d9e0e23c41a3` IDENTICAL | 26 → 21 | 3 | 2 lines |
| `Tools.ShippingKidFacts.kids_designCheck` | `Tools/ShippingKidFacts.lean` | `945071837d2c6af7` = `945071837d2c6af7` IDENTICAL | 31 → 26 | 26 | 2 lines |
| `Tools.ShippingMachineCausal.machine_traceL_of_loop_causalRA` | `Tools/ShippingMachineSeqLinkedR.lean` | `1295bf8e277a66e8` = `1295bf8e277a66e8` IDENTICAL | 35 → 30 | 25 | 2 lines |
| `Tools.ShippingMachineCausal.machine_traceL_of_comb_callsRA` | `Tools/ShippingMachineSeqLinkedR.lean` | `92e40510b94e7eed` = `92e40510b94e7eed` IDENTICAL | 25 → 20 | 7 | 2 lines |
| `Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA` | `Tools/ShippingMachineSeqLinkedR.lean` | `8cc40a5e43f4811d` = `8cc40a5e43f4811d` IDENTICAL | 31 → 26 | 28 | 2 lines |

(Binder counts are of the statement text; the four section variables of the first fourteen are
not counted. Proof lines moved: 264.)

An example of an old theorem's proof now (all seventeen have this shape):

    theorem kids_designCheck … (closes : MachineClosesAt mctx mref cctx cref c d.shape)
        (hon : …) (hoty : …) :
        Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
      kids_designCheck_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem kidOuts kidIns n hkid
        hcw hargs hpost (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes) hon hoty

## 5. The pin test — `Tests/Compiler/RanThreadingStatementsTest.lean` (new; GENERATED by `pintest`)

Target-only, asserting; `Tests/Compiler/RanSplitStatementsTest.lean` is NOT edited (it pins the
twenty statements of the first split and already asserts that the 31 `_ran` forms exist, are on the
standard axioms and are stated with `MachineRan` and without `MachineClosesAt` / `MachineCloses`
— the 17 of this unit are in its list under the same names, so it keeps checking them).

For each of the 17 theorems split here:

1. `example : <the statement at 80745d94, as a ∀, in full> := @<full name>` — the "型照合": the
   present constant has the old type up to definitional equality (binder order and types). The
   text is taken by the script from `git show 80745d94:<file>`, under the `open` lines in effect
   at the theorem (the namespace opened, not entered);
2. a `run_cmd`: the constant's leading binders' NAMES and KINDS against the list parsed from the
   old text (what 1. does not see);
3. the old theorem is on the standard axioms, and its proof term's direct constants contain its
   `_ran` form and `Tools.ShippingMachineRan.machineRan_of_closes` — it IS the corollary;
4. its `_ran` form exists, is on the standard axioms, mentions `MachineRan` and neither
   `MachineClosesAt` nor `MachineCloses`, and is declared in the SAME module as the old theorem
   (in place); the old statement still mentions `MachineClosesAt`.

PREDICTED log line: `RAN THREADING STATEMENTS: 17 threading theorems have their old statement …
their 17 _ran forms are present, …`.

## 6. What the integrator runs

Nothing to add to `lakefile.lean` (no new `Tools/` file; the test is in the `Tests` library) or to
`Tests/AllTests.lean` (the test is target-only).

1. `python3 scripts/ran_threading_split.py verify` — text only, seconds; PREDICTED 17 `IDENTICAL`
   lines and the `OK:` line (it is the output quoted in §4).
2. The nine files, in commit order: `Tools.ShippingChecksCoreGate`, `Tools.ShippingChecksWidths`,
   `Tools.ShippingChecksRaw`, `Tools.ShippingPortsMatchRaw`, `Tools.ShippingKidsSelf`,
   `Tools.ShippingChecksRunFacts`, `Tools.ShippingTextShipped`, `Tools.ShippingKidFacts`,
   `Tools.ShippingMachineSeqLinkedR`; then the stubs `Tools.ShippingKidFactsRan`,
   `Tools.ShippingMachineSeqLinkedRan`. NOTE: `ShippingChecksWidths` / `ShippingChecksRaw` are low
   in the import order — everything of the design-level chain above them rebuilds.
3. `Tools.ShippingOutermost`, `Tools.ShippingOutermostCommand`, `Tools.ShippingOutermostCoverage`,
   then `Tests.Compiler.MixDeepOutermostEndpointTest` (the generated outermost endpoint applies the
   `_ran` forms by name — same names, same statements; PREDICTED unchanged: standard axioms, 7
   proposition binders, `Start0` the one NOT ALLOWED) and `MixDeepOutermostRanTest` /
   `MixDeepOutermostTest`.
4. `Tests.Compiler.RanSplitStatementsTest` (PREDICTED unchanged: 20 pinned, 31 `_ran` forms) and
   `Tests.Compiler.RanThreadingStatementsTest` (§5).
5. `Tests.AllTests`; the census — PREDICTED unchanged, 134 declarations / 133 covered, `mixDeep`
   open; `#outermost_coverage` — PREDICTED unchanged ("outermost starts: 1 declaration [mixDeep]");
   `DepthSwitchPinTest` (in the suite) — PREDICTED unchanged (it fingerprints endpoint TYPES; no
   statement changed).
6. `#print axioms` of a few of the 17 old theorems and `_ran` forms: PREDICTED what they were
   (the standard three at most).

## 7. Risks, in order

1. **The seventeen corollaries** — the only NEW proof text Lean has not seen: one application
   each, positional explicit arguments in the `_ran` form's binder order (parsed by the script from
   the `_ran` statement), implicits (`nDecl`, `kidIns`, `M`, `b`, `D`, `c`, the four contexts; for
   the heads also `ι`, `α`, `ρ` and the `Inhabited` instances) left to unification from `hC`,
   `hargs`, `hpost` and the producer term. The same shape as the twelve corollaries of the first
   split, which built. If one fails it is an argument-order or unification error local to that
   theorem; the `_ran` form above it is unaffected.
2. **A `_ran` proof at its new position.** Built in a file that imports everything; now in its
   original's file. Every identifier in it is one the ORIGINAL proof used at that position (SCRIPT:
   equal up to the renames), and the renamed callees are either in the same file above it or in a
   file the original's callee came from. `simp` / `simpa` / `omega` calls see the simp set the
   original saw there. PREDICTED no difference.
3. **`open Tools.ShippingMachineTraceX (… machine_trace_lets_of_streamBRA_ran)`** in
   `ShippingMachineSeqLinkedR`: the name must exist in that namespace (it does:
   `Tools/ShippingMachineTraceX.lean`, first split). `machine_trace_lets_of_streamBRA` stays in
   the list although the three heads no longer call it (the `…R` forms below do not either; an
   unused name in an `open` list is not an error).
4. **Rebuild cost**: commits 2 and 3 touch files low in the chain; the whole design-level tower
   and every generated endpoint above it rebuilds (as for the first split: `Tests.AllTests`,
   everything downstream regenerated).
5. **The pin test's `run_cmd`**: `Name.appendAfter`, `Environment.getModuleIdxFor?`,
   `ConstantInfo.thmInfo` / `getUsedConstants` — names by reading; the binder comparison is the
   built test's code. The `example`s are in the built test's format; `core_portsMatch_raw`'s has
   the statement's `--` comments inside the `∀` binder list.
6. **Linter noise**: none expected beyond what the copies had (same texts).
7. **The stubs**: a file with imports and a module doc only. If a consumer needed something the
   copy file imported and the stub does not: the stubs keep the copy files' import lines exactly.

## 8. What I could not determine by reading

* Whether any of it elaborates.
* Whether any consumer inspects the MODULE of a `_ran` constant (none found by `grep`; the
  outermost command builds terms by name).
* Whether the proof terms of the old theorems being shorter changes anything measured elsewhere
  (e.g. a size or a time in a census) — statements are unchanged, so no pinned type moves.

## Integrator's build record (2026-10-14) — MEASURED; INTEGRATED on poc

Verified on the poc tree as ONE STACK with the projChain switch-over (runs `stack1`, `stack1b`, `stack1c`);
intermediate commits were not built one by one. `python3 scripts/ran_threading_split.py verify` on the
applied tree: 17 statements IDENTICAL to base, no import cycle.
Integrator fixes: (1) `Tools/ShippingChecksRaw.lean` — the script had inserted `core_raw_facts_ran`
between the original's `set_option maxHeartbeats … in` + docstring and its theorem (parse error
"unexpected token 'set_option'"); the block was moved back in front of `core_raw_facts`. No statement
changed; the other eight files do not have the pattern. (2) `Tests/Compiler/CoreDedupAuditTest.lean`
asserted that `core_raw_facts`' proof names `core_raw_factsM` DIRECTLY; after the split the tie is
`core_raw_facts` → `core_raw_facts_ran` → `core_raw_factsM_ran`; the audit now accepts either tie
(a check of proof structure, not of a statement).
Results: the nine split files, the two stubs and the outermost files build; `RanSplitStatementsTest` and
`RanThreadingStatementsTest` green ("17 threading theorems have their old statement …");
`MixDeepOutermostEndpointTest` green, `#outermost_coverage` unchanged (1 declaration);
`Tests.AllTests` 1348 jobs green; census unchanged (134 / 133).
