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
| UNMEASURED | no measurement exists |

The baseline column uses only declarations in db931dd4. Accepted work outside poc is listed in its own column and does
not change the baseline status.

**Update 2026-10-29 (G8 row only):** the corpus census of issue `sparkle-gaps-g8-measure` (reviewer-approved at
`par/g8-measure` 0cf85531) ran on poc eb5099fa, whose Lean tree equals db931dd4 (eb5099fa adds docs only). Its tool, its
control test and its record (scripts/gaps/G8_CENSUS_RESULT.md) are in poc through issue `sparkle-gaps-g8-int`. The G8
row's corpus-coverage cell now reports that measurement. No other row changed.

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

One row per binder or antecedent of the frozen telescope (35 rows) (scripts/c3/C4_STATEMENT.lean.txt; scripts/c5/C5_STATEMENT.lean.txt,
whose binder list is "IDENTICAL to C4's"). The C4 / C5 column gives the type where the two differ. Existential witnesses of the
conclusion (`ids`, `cache`, `regs`) are outputs, not binders, and are not listed.

| # | binder / antecedent | C4 type / C5 type | kind | gap(s) | baseline status | evidence |
|---|---|---|---|---|---|---|
| 1 | `P` | `MemSharedLeafParent` / `QSharedLeafParent` | CLASS-SCOPE | G8, G6 | CONTRACT (class member); members shown: `P_M`, `P_Q`, each CONDITIONAL on `hgrp` (G8 row) | `Tests.Compiler.CDef.P_M`, `Tests.Compiler.QDef.P_Q` (DECL); scripts/c3/C_CLASS.md:50-55 (TEXT) |
| 2 | `{mctx : Meta.Context}` | same | CONTRACT-runtime | G5 | universally quantified; constrained only by `hA` (#10) | C4_STATEMENT.lean.txt binder list (TEXT) |
| 3 | `{mref : ST.Ref … Meta.State}` | same | CONTRACT-runtime | G5 | universally quantified; constrained by `O`, `T` (#8, #9) | as #2 |
| 4 | `{cctx : Core.Context}` | same | CONTRACT-runtime | G5 | universally quantified; constrained by `hA` | as #2 |
| 5 | `{cref : ST.Ref … Core.State}` | same | CONTRACT-runtime | G5 | universally quantified; constrained by `O`, `T` | as #2 |
| 6 | `{w : Void IO.RealWorld}` | same | CONTRACT-runtime | G5 | start world; constrained by `hw` (#14) | as #2 |
| 7 | `{w1 : Void IO.RealWorld}` | same | RUN | no G row | end world of the run `hcore`. *Rationale:* an output of the run, not an assumption; it appears only in `hcore` | as #2 |
| 8 | `O : RefLawsAOps MkRefd mref cref` | same | CONTRACT-runtime | G5 | CONTRACT; runtime fit and joint satisfiability OPEN | `Tools.ShippingChildInvA.RefLawsAOps`, `Tools.ShippingChildFresh.MkRefd` (DECL); docs/parallel/open-items-by-kind.md:30-39, main-theorem-connection.md:38 (TEXT) |
| 9 | `T : RefLawsATele O.quiet mref cref` | same | CONTRACT-runtime | G5 | CONTRACT; an added boundary, unproved | `Tools.ShippingChildInvA.RefLawsATele` (DECL); main-theorem-connection.md:39 (TEXT) |
| 10 | `hA : AdmCtx O.quiet mctx cctx` | same | CONTRACT-runtime | G5 | CONTRACT. PROVED for `Command.mkMetaContext` only; "entry runs there" is a reading, not a theorem | `Tools.ShippingChildInvA.AdmCtx`, `Tools.ShippingStartWorldA.mkMetaContext_canUnfold` (DECL); main-theorem-connection.md:40 (TEXT) |
| 11 | `entryL : MachineDefines … P.leaf.decl P.leaf.d.shape` | memory-bearing leaf (`LeafPkg`) / PLAIN leaf (`QLeafPkg`) | CONTRACT-reflection | G3 | CONTRACT; validated per declaration by generated `rfl`s, not proved for all declarations. C5 additionally DERIVES the leaf's `MachineCloses` (`hcl_of_class`), so there is no `hcl` binder | `Tools.ShippingMachineEntry.MachineDefines`, `Tests.Compiler.QCloses.hcl_of_class` (DECL); open-items-by-kind.md §2; TrustBase.md:1662-1677; C5_STATEMENT.lean.txt:6-9 (TEXT) |
| 12 | `entryW : ∀ wp ∈ P.wrappers, MachineDefines … wp.decl wp.d.shape` | wrappers of the M class / `QWrapper P.leaf` (`.decl`/`.d` abbrevs of `pkg`) | CONTRACT-reflection | G3 | as #11 (no `MachineCloses` part) | as #11; C5_STATEMENT.lean.txt:8 (TEXT) |
| 13 | `entry : MachineDefines … P.top.decl P.top.d.shape` | same | CONTRACT-reflection | G3 | as #11 | as #11 |
| 14 | `hw : JQC O 0 w` | same | CONTRACT-runtime | G5 | CONTRACT (start-world invariant at depth 0) | `Tools.ShippingChildCacheA.JQC` (DECL); main-theorem-connection.md:41 (TEXT) |
| 15 | `{b : Module}` | same | RUN | no G row | the shipped module, fixed by `hpost` (#19). *Rationale:* named output of the run | C4_STATEMENT.lean.txt (TEXT) |
| 16 | `{raw : Module}` | same | RUN | no G row | the core result, fixed by `hcore` | as #15 |
| 17 | `{D : Design}` | same | RUN | no G row | the children's design, fixed by `hcore` | as #15 |
| 18 | `hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) … w (raw, D) w1` | same | RUN | no G row | CONTRACT. *Rationale:* a correctness statement of the form "if the compiler returns, the output is right"; no theorem claims a successful run exists | Audit §1; open-items-by-kind.md §5; main-theorem-connection.md:44; scripts/c3/GAP_MAP.md:16 "hcore, hpost, entry \| the run \| CONTRACT (the one actual run)" (TEXT) |
| 19 | `hpost : b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)` | same | RUN (post-processing) | no G row | CONTRACT. *Rationale:* this is the boundary between the theorem's run and what is shipped. The compiler's entries post-process the core result by `dropZeroWidthModule` and, in the full entry, `mergeChecked` (Sparkle/Compiler/Elab.lean:5600-5606, which is kept only if `refineCheck` accepts it). `hpost` names which of those two returned modules is `b`; it assumes nothing about the input | design record: C4_STATEMENT.lean.txt comment "the ONE actual compiler run and its post-processing"; scripts/c3/GAP_MAP.md:16; TrustBase.md:1029-1032 (`mergeChecked` checked by `refineCheck`) (TEXT) |
| 20 | `∀ i : Unit` | same | INPUT-CONDITION | no G row | the domain index (`dom := fun _ => defaultDomain`). *Rationale:* a quantified variable, not an assumption | C4_STATEMENT.lean.txt header (TEXT) |
| 21 | `∀ bools : Nat → Signal defaultDomain Bool` | same | INPUT-CONDITION | no G row | universally quantified. *Rationale:* every Bool input stream | as #20 |
| 22 | `∀ bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)` | same | INPUT-CONDITION | no G row | universally quantified. *Rationale:* every bit-vector input stream | as #20 |
| 23 | `∀ T' : Nat` | same | INPUT-CONDITION | no G row | universally quantified length | as #20 |
| 24 | `∀ ins : Nat → String → Nat` | same | INPUT-CONDITION | no G row | universally quantified: the IR input values per cycle; constrained by #28-#35 | as #20 |
| 25 | `∀ st0 : String → Nat` | same | INPUT-CONDITION | no G row | universally quantified: the IR start state; constrained by #28-#35 | as #20 |
| 26 | `∀ mems : MEnv` | same | INPUT-CONDITION | no G row | universally quantified: the start memory contents; constrained by #28-#35 | as #20 |
| 27 | `∀ kids : String → KT 2` | same | INPUT-CONDITION | no G row | universally quantified: the children's start states; constrained by #28-#35 | as #20 |
| 28 | `SourceInputs P.top.decl (P.top.d.bsIn.take P.nDecl) ids cache …` | same | INPUT-CONDITION | G3 | CONTRACT. It relates the streams to the reflected binders `ids` | C4_STATEMENT.lean.txt "input conditions (premises by design)" (TEXT) |
| 29 | regs pass: `∀ t st r, r ∈ regs → seedIn b ins t st r = st r` | same | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* the environment carries register state through `seedIn` (start-state convention) | C4_STATEMENT.lean.txt; scripts/c3/GAP_MAP.md:16-19 "input conditions" (TEXT) |
| 30 | `∀ t, ins t "rst" = 0` | same | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* reset held low, a clock/reset convention of the IR semantics (clk/rst-aware input fit, SRM29B) | scripts/c3/GAP_MAP.md "input conditions" row (TEXT) |
| 31 | `∀ t st, seedIn b ins t st "clk" = 0` | same | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* the clock wire convention, as #30 | as #30 |
| 32 | `hinit`: `regs[k]? = some r → slots[k]? = some f → st0 r = f.init` | same | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* registers start at their declared init. This replaced the removed `hstR` (C2) | scripts/c3/GAP_MAP.md hstR row (TEXT) |
| 33 | `ResetNk 2 raw D kids` | same | INPUT-CONDITION | G4, G8 | CONTRACT. The start state of a two-level instance tree; depth 2 is fixed by the class (`KSn 2`) | scripts/c3/GAP_MAP.md "ResetNk 2" (TEXT) |
| 34 | `hinsFit`: `x ∈ b.inputs → ins t x < 2 ^ declWidth b x` | same | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* input values fit their declared widths, an environment assumption | scripts/c3/GAP_MAP.md "hinsFit clk/rst-aware (SRM29B)" (TEXT) |
| 35 | `hstX`: open inputs not driven by an instance fit their widths at start | same | INPUT-CONDITION | no G row | CONTRACT. *Rationale:* start values of undriven wires fit their widths | C4_STATEMENT.lean.txt inner antecedent list (TEXT) |
| — | conclusion level: IR `runModuleTG` on `checkedOptimize b` | same | (scope of the conclusion) | G7, G1 | below the conclusion; the steps to `DesignSV` objects and then to the printed text are not part of C4/C5 | scripts/c3/GAP_MAP.md:35 "Not in C4's endpoint scope" (TEXT) |

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
| **G8 (new)** class coverage | — | **Two instances: membership CONDITIONAL, by proof.** `P_M` (topshareM) and `P_Q` (topshareQ) are constructed as class members under `hgrp : TmGrp` / `TqGrp`. `group` is a structural class assumption, and no proof of `TmGrp`/`TqGrp` is in poc. **Corpus coverage: MEASURED, upper bound incomplete** (update 2026-10-29; scripts/gaps/G8_CENSUS_RESULT.md, TEXT). The census reads every constant of 453 of the 459 frozen corpus modules (12134 constants) and evaluates shape-only conditions (T0) implied by the class fields. **20 are T0-eligible** (candidates only: `group`, the GEN-SHAPE fields and the full-data checks are not evaluated), all of them `Tests.Compiler` test tops; 7 pass M or Q strictly, 13 only as Q:PASS-noleafcall. **Within the measured modules, no IP/ or Examples/ declaration is eligible:** every IP PARENT fails T0, 12 on P3 (memory or memory-named entries in the top: 11 H.264, RV32 `rv32iCore`) and the YOLOv8 activation buffer on P1. Bound on member tops: ≤ 20 + 5652 UNEVALUATED-KIND (non-definition constants, unknown) + 0 READ-TIMEOUT + the constants of 6 unmeasured modules (count unknown; module 429 `Tests.IP.Net.TCPHeaderTest` OOMs alone, five do not build alone). A T0 FAIL is a non-membership only relative to the `MachineDefines` shape tie. `P_Q` is not an M member, so there is no unified class | `Tests.Compiler.CDef.P_M`, `Tests.Compiler.CDef.MemSharedLeafParent`, `Tests.Compiler.QDef.P_Q`, `Tests.Compiler.QDef.QSharedLeafParent`, `Tests.Compiler.Srm9ComposedTest.TmGrp`, `Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp`, `Tools.ShippingSharedLeafCensus.censusOne`, `Tests.Compiler.SharedLeafCensusControlTest.expectRow` (DECL); scripts/c3/C_CLASS.md:50-55, :99-104; scripts/gaps/G8_CENSUS_RESULT.md "Headline", "Unmeasured modules" (TEXT) | — | proofs of `TmGrp`/`TqGrp` or deriving `group` (G-GRP-DERIVE, optional); the census bound's open terms (6 unmeasured modules, the UNEVALUATED-KIND term) and full membership of the 20 candidates; classes for other shapes, in particular tops with memory entries (the P3 failures of the IP designs) (main-theorem-connection.md:48 "class generalisation … OPEN (L8s)", TEXT); one unified class | **yes:** `P` |

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

**Evidence check (rev2, namespace-aware):** the declaration-aware check of freeze Amendment 3 ran over every DECL cited above.
- **Source:** `git show db931dd4:<path>`, with block comments and docstrings removed, then line comments.
- **Scope tracking:** `namespace N`, `section` and `mutual` push onto a scope stack, and `end` pops one entry.
- **Qualified names:** each declaration header's identifier is qualified with the open namespaces, or taken verbatim after
  `_root_.`.
- **Match rule:** a pair passes only if its EXACT fully-qualified name is declared in the cited file. Short names and other
  namespaces do not match. Negative test: `memSharedLeaf_ships` and `Tests.Compiler.QDef.memSharedLeaf_ships` at
  C4ComposedTest.lean both report MISSING.
- **Result:** 53 DECL pairs, 53 found, 0 missing, and 0 GENERATED cited. Each short name in §1/§2 resolved to exactly one
  declaration in its file.
- **Update 2026-10-29:** pairs 54-55 (G8 row) are in files added by `sparkle-gaps-g8-int`. They are checked by the same
  script at that issue's head instead of db931dd4: 2 found, 0 missing.
- **TEXT citations:** each was opened at the cited line(s) at db931dd4.
- The script and pair list are in the review note and are not committed.

The table below is the exact pair list. A short name in §1/§2 refers to the entry below with the same last component and file.

| # | fully-qualified declaration | file |
|---|---|---|
| 1 | `Tests.Compiler.C4Composed.memSharedLeaf_ships` | Tests/Compiler/C4ComposedTest.lean |
| 2 | `Tests.Compiler.C4Composed.FrozenC4` | Tests/Compiler/C4ComposedTest.lean |
| 3 | `Tests.Compiler.CDef.MemSharedLeafParent` | Tests/Compiler/CDefTest.lean |
| 4 | `Tests.Compiler.C4Final.topshareM_hierC_of_class` | Tests/Compiler/C4FinalTest.lean |
| 5 | `Tests.Compiler.QFinal.qSharedLeaf_ships` | Tests/Compiler/QFinalTest.lean |
| 6 | `Tests.Compiler.QDef.FrozenC5` | Tests/Compiler/QDefTest.lean |
| 7 | `Tests.Compiler.QDef.QSharedLeafParent` | Tests/Compiler/QDefTest.lean |
| 8 | `Tests.Compiler.QFinal.topshareQ_hierC_of_class` | Tests/Compiler/QFinalTest.lean |
| 9 | `Tests.Compiler.QCloses.hcl_of_class` | Tests/Compiler/QClosesTest.lean |
| 10 | `Tools.ShippingMachineClosesData.closes_of_data` | Tools/ShippingMachineClosesData.lean |
| 11 | `Tools.ShippingSrm33.machine_ships_hierC_noHstR` | Tools/ShippingSrm33Core.lean |
| 12 | `Tests.Compiler.CDef.P_M` | Tests/Compiler/CDefTest.lean |
| 13 | `Tests.Compiler.QDef.P_Q` | Tests/Compiler/QDefTest.lean |
| 14 | `Tools.ShippingChildInvA.RefLawsAOps` | Tools/ShippingChildInvA.lean |
| 15 | `Tools.ShippingChildFresh.MkRefd` | Tools/ShippingChildFresh.lean |
| 16 | `Tools.ShippingChildInvA.RefLawsATele` | Tools/ShippingChildInvA.lean |
| 17 | `Tools.ShippingChildInvA.AdmCtx` | Tools/ShippingChildInvA.lean |
| 18 | `Tools.ShippingStartWorldA.mkMetaContext_canUnfold` | Tools/ShippingStartWorldA.lean |
| 19 | `Tools.ShippingMachineEntry.MachineDefines` | Tools/ShippingMachineEntry.lean |
| 20 | `Tools.ShippingChildCacheA.JQC` | Tools/ShippingChildCacheA.lean |
| 21 | `Tools.ShippingSrm4Core2.core_hierGate_anyAM` | Tools/ShippingSrm4Core2.lean |
| 22 | `Tests.Compiler.C4Ships.kidsMasked_of_class` | Tests/Compiler/C4ShipsTest.lean |
| 23 | `Tests.Compiler.QShips.kidsMasked_of_class` | Tests/Compiler/QShipsTest.lean |
| 24 | `Tools.ShippingSrm4Parent.kidsNC_maskedN` | Tools/ShippingSrm4Parent.lean |
| 25 | `Tools.ShippingSrm4Parent.kidsNC_runFacts` | Tools/ShippingSrm4Parent.lean |
| 26 | `Tools.ShippingSrm4Parent.kidsNC_designCheck_of_kidsPass` | Tools/ShippingSrm4Parent.lean |
| 27 | `Tools.ShippingChecksDerived.leaf_run_outsCheck` | Tools/ShippingChecksDerived.lean |
| 28 | `Tools.ShippingChecksDerived.leaf_run_kids` | Tools/ShippingChecksDerived.lean |
| 29 | `Tools.ShippingLegacySem.legacy_translate_contract` | Tools/ShippingLegacySemContract.lean |
| 30 | `Tools.ShippingLegacySem.proj_entry_output` | Tools/ShippingLegacySemProj.lean |
| 31 | `Tools.ShippingLegacySem.tuple_entry_output` | Tools/ShippingLegacySemTupleEntry.lean |
| 32 | `Tools.ShippingChildLegacyTailA.legacyTailA_generic` | Tools/ShippingChildLegacyTailA.lean |
| 33 | `Tools.ShippingReaderTerm.readTerm_sound` | Tools/ShippingReaderTerm.lean |
| 34 | `Tools.ShippingReaderNodes2.readTerm2_sound` | Tools/ShippingReaderNodes2.lean |
| 35 | `Tools.ShippingReaderComplete.readTerm_quote` | Tools/ShippingReaderComplete.lean |
| 36 | `Tools.ShippingReaderFuel.eval_iff` | Tools/ShippingReaderFuelEval.lean |
| 37 | `Tools.ShippingReaderFuel.driveShape_complete` | Tools/ShippingReaderFuelDriverComplete.lean |
| 38 | `Tools.ReaderFuelGeneric.fixpoint_not_complete` | Tools/ReaderFuelGeneric.lean |
| 39 | `Tools.ShippingSrm22Width.SourceRegsKept` | Tools/ShippingSrm22Width.lean |
| 40 | `Tools.ShippingChildTranslateA.fuelFix_of` | Tools/ShippingChildTranslateA.lean |
| 41 | `Tools.ShippingReaderFuel.fuel_mono` | Tools/ShippingReaderFuelKleene.lean |
| 42 | `Tools.ShippingChildInvA.InertUnfold` | Tools/ShippingChildInvA.lean |
| 43 | `Tools.ShippingChildInvA.FramedA` | Tools/ShippingChildInvA.lean |
| 44 | `Tools.ShippingChildInvA.RefLawsCore.toAOps` | Tools/ShippingChildInvA.lean |
| 45 | `Tools.ShippingOkMsgGoal.not_okMsg_of_hasGoal` | Tools/ShippingOkMsgGoal.lean |
| 46 | `Tools.ShippingHeapModel.heapLaws_sat` | Tools/ShippingHeapModel.lean |
| 47 | `Tools.ShippingHeapProvenance.allocIn_ne_valid` | Tools/ShippingHeapProvenance.lean |
| 48 | `Tools.ShippingDesignWriterRun.writer_prints_endpoint_artifact` | Tools/ShippingDesignWriterRun.lean |
| 49 | `Tools.ShippingModuleName.ofDecl_injective` | Tools/ShippingModuleName.lean |
| 50 | `Tools.ShippingModuleName.decode_encode` | Tools/ShippingModuleName.lean |
| 51 | `Sparkle.IR.ModuleName.ofDecl` | Sparkle/IR/ModuleName.lean |
| 52 | `Tests.Compiler.Srm9ComposedTest.TmGrp` | Tests/Compiler/Srm9ComposedTest.lean |
| 53 | `Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp` | Tests/Compiler/Srm4ComposedQTest.lean |
| 54 | `Tools.ShippingSharedLeafCensus.censusOne` | Tools/ShippingSharedLeafCensus.lean |
| 55 | `Tests.Compiler.SharedLeafCensusControlTest.expectRow` | Tests/Compiler/SharedLeafCensusControlTest.lean |
