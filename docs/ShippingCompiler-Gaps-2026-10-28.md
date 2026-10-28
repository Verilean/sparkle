# General-theorem gaps at poc db931dd4 (2026-10-28)

This refreshes the status of docs/ShippingCompiler-GeneralTheorem-Audit.md §0/§7, which was dated 2026-10-12. Plan:
`scripts/gaps/GAP_TABLE_FREEZE.md`, freeze approved at 0af7efb1.

**Baseline** is `poc/roundtrip-proof` db931dd48e9da2dd9eea92ad1e05dfbc2503bea3.
- Its Lean tree equals 7c70632c plus docs commits.
- Build record: scripts/int/C45_POC_MANIFEST.md, "Build evidence".
- `Tests.AllTests` at db931dd4: job `c45-poc-all-db931dd4`, exit 0, 1687 jobs.

**Status words:**

| word | meaning |
|---|---|
| PROVED | kernel theorem, built |
| CONDITIONAL | proved relative to the listed premises |
| OPEN | not proved |
| REFUTED | counterexample reproduced |
| TRUSTED | trusted by design |
| CONTRACT | premise by design |
| MEASURED | observed on named declarations, not proved |

The baseline column uses only declarations in db931dd4. Accepted work outside poc is listed in its own column and does
not change the baseline status.

**Evidence check classes:**
- **DECL:** a declaration header found in the cited file at db931dd4, with comments stripped.
- **GENERATED:** a generating command plus a job that elaborated the file. No GENERATED item is cited below.
- **TEXT:** a reviewed docs record, cited by path and line.

Every DECL is listed with its file. The check result is in §4.

## 1. The C4/C5 statements and their premises

**The two theorems:**
- **C4:** `memSharedLeaf_ships` (Tests/Compiler/C4ComposedTest.lean, DECL), over `MemSharedLeafParent` (Tests/Compiler/CDefTest.lean,
  DECL).
  - Audited against `FrozenC4` (C4ComposedTest.lean, DECL).
  - Instance corollary: `topshareM_hierC_of_class` (Tests/Compiler/C4FinalTest.lean, DECL).
- **C5:** `qSharedLeaf_ships : FrozenC5` (Tests/Compiler/QFinalTest.lean, DECL; `FrozenC5` in Tests/Compiler/QDefTest.lean,
  DECL), over `QSharedLeafParent` (QDefTest.lean, DECL).
  - Instance corollary: `topshareQ_hierC_of_class` (QFinalTest.lean, DECL).
- **Builds:**
  - C4ComposedTest, C4FinalTest and CDefTest: c45-x00-7c70632c, exit 0.
  - QDefTest and QFinalTest: c45-x02-7c70632c, exit 0.
- **Acceptance:** sparkle-gen-c4 (692d78e3) and sparkle-gen-c5-qshape (a942e6ac) were accepted by the reviewer on 2026-10-28,
  as recorded in the manager issue notes.

Both statements have the same 19 binders: `P; {mctx mref cctx cref w w1}; O T hA entryL entryW entry hw; {b raw D}; hcore
hpost`. The binder audits are in C4ComposedTest and QFinalTest.

C5 differs only in the types:
- `P : QSharedLeafParent`.
- The leaf is plain, and `entryW` ranges over `QWrapper P.leaf`.
- There is no `hcl` binder. The leaf's `MachineCloses` is derived by `hcl_of_class` (Tests/Compiler/QClosesTest.lean, DECL) via
  `closes_of_data` (Tools/ShippingMachineClosesData.lean, DECL).

The conclusion, verbatim from `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean, DECL), is this. For every input
stream, every `T'` and every start state satisfying the input conditions, `runModuleTG … (checkedOptimize b).body` with
children from `D.modules` produces `T'` environments whose outputs equal the source. This is an IR-level conclusion. It is
not `DesignSV` and not text.

| binder / antecedent | kind | gap(s) | baseline status | evidence |
|---|---|---|---|---|
| `P` | CLASS-SCOPE | G8, G6 | CONTRACT (class member). Membership of a source is shown only for `P_M`/`P_Q`, each taking `hgrp` | `P_M` (Tests/Compiler/CDefTest.lean, DECL), `P_Q` (Tests/Compiler/QDefTest.lean, DECL); scripts/c3/C_CLASS.md:50-55 (TEXT, `group` = structural class assumption) |
| `O : RefLawsAOps MkRefd mref cref` | CONTRACT-runtime | G5 | CONTRACT; runtime fit and satisfiability OPEN | `RefLawsAOps` (Tools/ShippingChildInvA.lean, DECL), `MkRefd` (Tools/ShippingChildFresh.lean, DECL); docs/parallel/open-items-by-kind.md:30-39 (TEXT) |
| `T : RefLawsATele O.quiet mref cref` | CONTRACT-runtime | G5 | CONTRACT; an added boundary, unproved | `RefLawsATele` (Tools/ShippingChildInvA.lean, DECL); docs/parallel/main-theorem-connection.md:39 (TEXT) |
| `hA : AdmCtx O.quiet mctx cctx` | CONTRACT-runtime | G5 | CONTRACT. The command start is PROVED only for the plain meta context; the link to the actual entry is "a reading, not a theorem" | `AdmCtx` (Tools/ShippingChildInvA.lean, DECL), `mkMetaContext_canUnfold` (Tools/ShippingStartWorldA.lean, DECL); main-theorem-connection.md:40 (TEXT) |
| `entryL`, `entryW`, `entry : MachineDefines …` | CONTRACT-reflection | G3 | CONTRACT; checked per declaration by generated `rfl`s, not proved for all declarations | `MachineDefines` (Tools/ShippingMachineEntry.lean, DECL); open-items-by-kind.md §2 (TEXT); TrustBase.md:1662-1677 (TEXT) |
| `hw : JQC O 0 w` | CONTRACT-runtime | G5 | CONTRACT (start-world invariant) | `JQC` (Tools/ShippingChildCacheA.lean, DECL) |
| `hcore : RunsTo (synthesizeCombinationalCore …)` | RUN | no G row | CONTRACT. The theorem is about a successful run; no theorem claims one exists. *Rationale:* a correctness statement of the form "if the compiler returns, the output is right" (Audit §1; open-items-by-kind §5; main-theorem-connection.md:44) | open-items-by-kind.md §5 (TEXT) |
| `hpost` (zero-width drop, optional `mergeChecked`) | RUN | no G row | CONTRACT. It names the two post-processing results the compiler can return. *Rationale:* it describes what the compiler did; it is not an assumption about the input | scripts/c3/C4_STATEMENT.lean.txt (TEXT, binder list) |
| inner `SourceInputs …` | INPUT-CONDITION | G3 | CONTRACT. It relates the streams to the source's inputs through the reflected binders | C4_STATEMENT.lean.txt "input conditions (premises by design)" (TEXT) |
| inner regs-pass, `hinit` (start = slot inits), `hstX` | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* they state the environment's start state (registers at their declared init, unconstrained wires fitting their widths), as recorded in the C4_STATEMENT comment and the GAP_MAP hstR row | C4_STATEMENT.lean.txt; scripts/c3/GAP_MAP.md hstR row (TEXT) |
| inner `rst = 0`, `clk = 0` | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* a clock/reset convention of the IR semantics (SRM29B, clk/rst-aware input fit) | scripts/c3/GAP_MAP.md "input conditions" row (TEXT) |
| inner `ResetNk 2 raw D kids` | INPUT-CONDITION | G4 (depth fixed at 2), G8 | CONTRACT. It is the start state of a two-level instance tree. The depth 2 is part of the class (C4/C5 fix `KSn 2`) | scripts/c3/GAP_MAP.md "ResetNk 2" (TEXT) |
| inner `hinsFit` (inputs fit their widths) | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* an environment assumption on input values, as in the GAP_MAP input-conditions row | scripts/c3/GAP_MAP.md (TEXT) |
| conclusion level: IR `runModuleTG` on `checkedOptimize b` | (scope of the conclusion) | G7, G1 | Below the conclusion, the steps to the design objects and then to the printed text are not part of C4/C5 | scripts/c3/GAP_MAP.md "Not in C4's endpoint scope" (TEXT) |

**Not binders any more, derived inside C4/C5 (PROVED within the class):**
- `hierGate`, through `core_hierGate_anyAM` (Tools/ShippingSrm4Core2.lean, DECL).
- `kidsMaskedN`, through `kidsMasked_of_class` (Tests/Compiler/C4ShipsTest.lean, DECL; Tests/Compiler/QShipsTest.lean, DECL).
- `hierRefineCheck`: case-split inside `machine_ships_hierC_noHstR`, both branches handled.
- `hstR`, `hinitW`, `soundL`, `composed`, `facts`, `Bnd`/`Bd`.

## 2. Gap table

| gap | status 2026-10-12 (Audit §0/§7) | baseline at db931dd4 | evidence in poc | accepted outside poc | what remains open | C4/C5 depend? |
|---|---|---|---|---|---|---|
| **G1** output checks are obligations | open; first unit for machines without calls (`leaf_run_outsCheck`) | **CONDITIONAL, within the C4/C5 classes:** the checks they need (`hierGate`, `kidsMaskedN`, `hierRefineCheck` case-split) are derived from the run. **OPEN in general** | `core_hierGate_anyAM` (Tools/ShippingSrm4Core2.lean, DECL); `kidsMasked_of_class` (C4ShipsTest.lean, QShipsTest.lean, DECL); `kidsNC_maskedN`, `kidsNC_runFacts`, `kidsNC_designCheck_of_kidsPass` (Tools/ShippingSrm4Parent.lean, DECL); `leaf_run_outsCheck`, `leaf_run_kids` (Tools/ShippingChecksDerived.lean, DECL) | — | checks for sources outside the two classes; `kidsPass` (the children part of `designCheck`) for designs with a memory module (Tools/ShippingSrm4Parent.lean:6, TEXT); no text conjunct derived from a run beyond the guards (docs/parallel/G1-designCheck-text.md:9, TEXT) | no (derived), within the class |
| **G2** legacy route has no source theorem | open; contract layer CONDITIONAL; cache-rollback defect reproduced, fix not applied | **CONDITIONAL:** contract on `LegacyDom`, whose inline case needs `ReachesUnfold` (undischarged); class-level output theorems keep a `MemoHit ∨ …` disjunct; no real fallback declaration covered end to end. **The cache-rollback fix is integrated** | `legacy_translate_contract` (Tools/ShippingLegacySemContract.lean, DECL); `proj_entry_output` (Tools/ShippingLegacySemProj.lean, DECL); `tuple_entry_output` (Tools/ShippingLegacySemTupleEntry.lean, DECL); fix integrated b7971f83 (docs/ShippingCompiler-FinalGoal.md:313-315, TEXT; docs/parallel/G2-legacy.md:700-720, TEXT). Runtime-invariant tail only: `legacyTailA_generic` (Tools/ShippingChildLegacyTailA.lean, DECL) | — | `ReachesUnfold`; the memo-hit disjunct; legacy-route semantics end to end (main-theorem-connection.md:49, TEXT); cost of the fix on large designs | no (machine route; the legacy tail is kept only as a runtime invariant) |
| **G3** reader soundness / source↔MachineData / generator coverage | open; strict reader sound (18 kinds) and complete (11); `machineShape?` is `partial` | **OPEN:** reflection (`MachineDefines`) is a premise, validated per declaration. The strict reader is PROVED but not run by the compiler. A fuel-total reader candidate is PROVED in isolation; production is not switched (MEASURED shadow 40/40) | `readTerm_sound` (Tools/ShippingReaderTerm.lean, DECL); `readTerm2_sound` (Tools/ShippingReaderNodes2.lean, DECL); `readTerm_quote` (Tools/ShippingReaderComplete.lean, DECL); `eval_iff` (Tools/ShippingReaderFuelEval.lean, DECL); `driveShape_complete` (Tools/ShippingReaderFuelDriverComplete.lean, DECL); `fixpoint_not_complete` (Tools/ReaderFuelGeneric.lean, DECL); docs/parallel/R-reader-switch-boundary.md:34-37, :50 "no production switch is planned" (TEXT) | — | `MachineDefines` for all declarations (premise per declaration, main-theorem-connection.md:36, :43, TEXT); the unmodelled O1/O2/O3 for a production switch (R-reader-switch-boundary.md:34-37, TEXT) | **yes:** `entryL`/`entryW`/`entry`, `SourceInputs` |
| ↳ SRM-G3 `SourceRegsKept` (separate namespace, milestone `sparkle-g3`) | — | **OPEN:** the definition exists, and nothing proving it is in poc | `SourceRegsKept` (Tools/ShippingSrm22Width.lean, DECL) | exact-gap settlement `kjob/g3-settle` 08c46310 (scripts/g3/G3_SETTLEMENT.md, accepted by the user 2026-10-28 as a settlement, NOT a proof). Ten route-R rows rest on `partial def`s, plus the bridges `kjob/g3-mqclose2` fd2c494d, `kjob/g4-mq-supply` 0342f035; none is an ancestor of db931dd4 | the ten route-R rows; the rows→`SourceRegsKept` composition | **no** (scripts/c3/GAP_MAP.md: "G3 NOT needed for this route") |
| **G4** fuel / depth | open: (a) monotonicity provable, (b) equivalence with `partial` cannot be stated | **OPEN:** fuel induction (`fuelFix_of`) exists; no monotonicity theorem for the translator's fuel fixpoint; the limits (depth 1024, fuel 2^20) are fixed constants and a recorded behaviour change | `fuelFix_of` (Tools/ShippingChildTranslateA.lean, DECL); `fuel_mono` for the isolated reader candidate only (Tools/ShippingReaderFuelKleene.lean, DECL); TrustBase.md:449, :666-668 (TEXT) | — | translator fuel monotonicity; "enough fuel reproduces a finite successful run"; all-fuel `StartDomOk` (main-theorem-connection.md:37, TEXT) | indirectly: depth is fixed at 2 (`ResetNk 2`/`KSn 2`); the run `hcore` is under the fixed limits |
| **G5** runtime laws | conditional; no runtime model; `profLog`; T3 trusted | **CONTRACT / OPEN.** The new boundary `RefLawsAOps`/`RefLawsATele`/`AdmCtx`/`JQC` is a premise; runtime fit and joint satisfiability are OPEN. **REFUTED against the old `RefLaws.frame`** (every-context quantification meets `canUnfold?`), which is why the boundary was replaced. The heap laws are satisfied only by a pure restatement | `RefLawsAOps`, `RefLawsATele`, `AdmCtx`, `InertUnfold`, `FramedA`, `toAOps` (Tools/ShippingChildInvA.lean, DECL); `MkRefd` (Tools/ShippingChildFresh.lean, DECL); `JQC` (Tools/ShippingChildCacheA.lean, DECL); `not_okMsg_of_hasGoal` (Tools/ShippingOkMsgGoal.lean, DECL); probe Tests/Compiler/CanUnfoldProbe.lean (814a9a81, open-items-by-kind.md:31, TEXT); `heapLaws_sat` (Tools/ShippingHeapModel.lean, DECL); `allocIn_ne_valid` (Tools/ShippingHeapProvenance.lean, DECL) | — | fit to Lean's real runtime (`@[extern]` refs, `Void IO.RealWorld`, Meta primitives); joint satisfiability of the new laws (a model is not exhibited); refs at the first entry (R13/R14); commands between entries | **yes:** `O`, `T`, `hA`, `hw` |
| **G6** final statement shape | no quantified Lean statement | **CLASS-generic statements PROVED** (C4, C5: ∀ P in the class, ∀ inputs/T'); **OPEN as a statement over every source.** No Lean def quantifies over every accepted source | `memSharedLeaf_ships`, `FrozenC4` (C4ComposedTest.lean, DECL); `qSharedLeaf_ships` (QFinalTest.lean, DECL), `FrozenC5` (QDefTest.lean, DECL); main-theorem-connection.md:44 (TEXT) | — | an every-source statement; a unified M+Q class (reviewer note on sparkle-gen 2026-10-28: a separate, unsatisfied scope) | they ARE the current form |
| **G7** printer | trusted by design | **TRUSTED:** forward simulation to the emitted design objects is PROVED for the `_sat` endpoints; the printed bytes are trusted; parse-back is validation only | `writer_prints_endpoint_artifact` (Tools/ShippingDesignWriterRun.lean, DECL); TrustBase.md:1635-1659 (TEXT); open-items-by-kind.md §4 (TEXT) | — | the printer; **for C4/C5 additionally** the step from the IR conclusion (`runModuleTG`) to `DesignSV` objects | yes, below their conclusion |
| **N1** name separation | done for generated closings; open in general (`Name.toString` not injective) | **PROVED for compiler module names** (an injective `ofDecl` encoding used by the compiler). **OPEN:** output port vs `inst{k}_…` names (`hfresh` stays), arbitrary strings, shared descendants | `ofDecl_injective`, `decode_encode` (Tools/ShippingModuleName.lean, DECL); `ofDecl` (Sparkle/IR/ModuleName.lean, DECL); docs/parallel/B-name-discharge.md:62, rows 11/13 (TEXT) | — | `hfresh`; shared descendants (`mixDeep`) | no name binder in C4/C5 |
| **G8 (new)** class coverage | — | **MEASURED, for two instances:** `P_M` (topshareM) and `P_Q` (topshareQ), each CONDITIONAL on `hgrp : TmGrp`/`TqGrp` (`group` is a structural class assumption; no proof of `TmGrp`/`TqGrp` in poc). No measurement of how many compiler-accepted sources are members. `P_Q` is not an M member | `P_M`, `MemSharedLeafParent` (CDefTest.lean, DECL); `P_Q`, `QSharedLeafParent` (QDefTest.lean, DECL); `TmGrp` (Tests/Compiler/Srm9ComposedTest.lean, DECL); `TqGrp` (Tests/Compiler/Srm4ComposedQTest.lean, DECL); scripts/c3/C_CLASS.md:50-55, :99-104 (TEXT) | — | deriving `group` (G-GRP-DERIVE, optional); a corpus membership measurement; classes for other shapes (main-theorem-connection.md:48 "class generalisation … OPEN (L8s)", TEXT); one unified class | **yes:** `P` |

### Corrections (sources that disagree; the later reviewed record wins)
1. **The freeze "Why" (scripts/gaps/GAP_TABLE_FREEZE.md:14) says the G3 exact-gap settlement has landed in poc. It has
   not:**
   - `scripts/g3/` is absent at db931dd4.
   - 08c46310 and its base are not ancestors of db931dd4.
   - db931dd4 records it only as text (scripts/int/C45_POC_MANIFEST.md:80).

   This table lists it under "accepted outside poc".
2. **The Audit §0 G2 row ("fix not applied", 2026-10-12)** is superseded by FinalGoal.md:313-315: the fix was integrated
   at b7971f83.
3. **The Audit §0 N1 row ("`Name.toString` not injective")** is superseded for module names by the `ofDecl` encoding;
   `hfresh` still stays.
4. **The comment "G1 refuted for actual M/Q" in scripts/c3/C4_STATEMENT.lean.txt** refers to SRM22's `InputsAreWires`,
   not Audit G1.

## 3. Not claimed
- No CI, no production change and no push. Builds are local kjob runs, recorded in the C45 manifest.
- No G row is complete unless it reads PROVED with evidence. No row here reads PROVED for the general case.
- The C4/C5 conclusions hold relative to their contract binders (G3 reflection, G5 runtime) and the class (G8). They stop
  at the IR semantics (G7).
- Choosing the next unit and accepting `sparkle-gen` at the two-class scope are the user's decisions.

## 4. Sources and evidence check
**Sources:**
- docs/ShippingCompiler-GeneralTheorem-Audit.md §0/§7;
- docs/parallel/open-items-by-kind.md;
- docs/parallel/main-theorem-connection.md;
- docs/parallel/G2-legacy.md;
- docs/parallel/G1-designCheck-text.md;
- docs/parallel/R-reader-switch-boundary.md;
- docs/parallel/B-name-discharge.md;
- docs/ShippingCompiler-FinalGoal.md;
- docs/ShippingCompiler-TrustBase.md;
- scripts/c3/{C4_STATEMENT.lean.txt, C_CLASS.md, GAP_MAP.md};
- scripts/c5/{C5_STATEMENT.lean.txt, GAP_MAP.md};
- scripts/int/C45_POC_MANIFEST.md;
- manager notes of sparkle-gen, sparkle-gen-c4, sparkle-gen-c5-qshape and sparkle-g3.

**Evidence check:** a declaration-aware check (freeze Amendment 3) ran over every DECL above:
- **Source:** `git show db931dd4:<path>` for each cited file.
- **Comment stripping:** block comments and docstrings were removed, then line comments.
- **Header match:** a declaration header regex with optional namespace prefix.
- **Result:** 53 DECL pairs, 53 found, 0 missing (0 GENERATED cited). TEXT citations were each opened at the cited line(s) at db931dd4 by the author. Command: `declcheck.py REPO db931dd4 pairs.tsv` (script and pair list in the review note, not committed).
