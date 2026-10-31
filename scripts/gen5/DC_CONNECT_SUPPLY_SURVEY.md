# DC-CONNECT: supply of the real EntryWitness (O1 / O3 / DeclConnect / NV-witness) — survey + freeze of the first unit

Issue `sparkle-gen5-dc-connect`, agent g5dc-r8, base `kjob/g5dc-r7` 6bd33fd7 (R1/R2 scoped approved; clean build dc7v-6bd33fd7). Extends `DC_CONNECT_FREEZE.md` (§C.3, §C.7). **Design only; no Lean in this commit.**
Wording: "unsupplied / this survey found no route" describes THIS survey (files grepped: this tree, `kjob/g5rk-r10`, `kjob/g5rk-r11`, `par/gen5-t2`), not impossibility. A "mutant" is a rejection by signature/defeq of a well-typed changed statement, not a semantic counterexample.
`FG_COND` / `FG_CONNECT` stay CONDITIONAL; this is not FG completion. core / opaque exploration boundaries of the closure check remain. No new law/TRUSTED, no shared-definition or compiler edit, FG not narrowed, `GenWF` not strengthened.

## 1. What "supplying the EntryWitness" means (read from `Tools/ShippingGen5FG.lean`)
`EntryWitness` is a HYPOTHESIS of `FG_COND`/`FG_CONNECT` (universally quantified). Nothing needs to *construct* a witness for the statements to be well formed. What the final theorem needs, for ANY witness
`EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D` (`Start L mctx cctx w`, route disjunct `RunsTo (synthesizeCombinational declName) … w (b, D) w'` ∨ `RunsTo (synthesizeCombinationalWithParameters declName parameters) … w (b, D) w'`, `ReflectsAll L declName parameters`), is to DERIVE:
- **O1** `∃ raw, Post b raw`;  **O2** `∃ p, GP (envAt cref w) declName = some p`;  **O3** `∀ raw, Post b raw → ∃ p n, GP … = some p ∧ TopShips p n declName b raw D`;  **DC** `DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)`.
**NV-witness** (an `EntryWitness` EXISTS) is a different thing: it is only needed for non-vacuity of `FG_CONNECT`, and only execution evidence (a corpus run) exists; the survey found no Lean term of a run (no route to a Lean-level existence; not a claim of impossibility).

## 2. Supplier table (each approved part with its real name and full type; each premise row with status)
`[T]` = this tree, `[r10]` = `kjob/g5rk-r10` 8bed2e00, `[r11]` = `kjob/g5rk-r11` e87a2251 (U8 design approved, no Lean), `[t2]` = `par/gen5-t2`. Owner column: the Issue that owns the row (no duplicate implementation here).

| # | row needed | supplier (real name, location) | full type / statement (abridged where long) | status | owner |
|---|---|---|---|---|---|
| S1 | default route ⇒ a CORE run and the post-processing of its result | `synthesizeCombinational_reads` [T] `Tools/ShippingPostSoundness.lean:583` | `RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M',D') w' → ∃ M D w1, RunsTo (synthesizeCombinationalCore declName [] false) … w (M,D) w1 ∧ (M' = dropZeroWidthModule M ∨ M' = mergeDuplicates (dropZeroWidthModule M))` | **Exists, but its post-processing disjunct is `mergeDuplicates`, not `mergeChecked`.** `RefineCheck.mergeChecked_cases : mergeChecked m = mergeDuplicates m ∨ mergeChecked m = m` (`Sparkle/IR/RefineCheck.lean:280`), so the stated disjunct does NOT give the relation `T1Stmt` uses (`b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)`, `Tools/ShippingGen2Defs.lean:362-364`) | existing file |
| S2 | the `Post` relation of the default entry (O1/O3) | `T1Stmt`'s hypothesis [T] `Tools/ShippingGen2Defs.lean:362-364` | `b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)` | text exists; `Post` itself is M4's parameter and is NOT fixed in Lean (GENERAL_SPEC.md:98) | `sparkle-gen4-fg-assembly` (M4 assembly; where `Post` is fixed; no narrower existing Issue found by this survey) |
| S3 | parametric route ⇒ anything | — | `synthesizeCombinationalWithParameters` occurs in `Tools/` only in `Tools/ShippingGen5FG.lean` (this survey's grep, on the surveyed base/branches only) | **Unsupplied in the surveyed base: this survey found no route** (the machine route is disabled there: `Elab.lean:5072-5075`; `GP env₀ declName` may be `none`) | `sparkle-gen4-parametric-supply` (parametric route supply; M4), `sparkle-gen5-dg-cover` for coverage |
| S4 | core run ⇒ linked chain (`coreHead`, `getConstInfo`, `getEnv`, `synthesizeFromConst`, `coreFinally`) | `Tools.ShippingEntryReadsLinked.core_chain` [T] `:165` | `RunsTo (synthesizeCombinationalCore declName [] false) … w (M,D) w' → ∃ s w1 envR ci w2 w3 w4, RunsTo (coreHead declName) … w s w1 ∧ RunsTo (getConstInfo declName) … w1 ci w2 ∧ RunsTo getEnv … w2 envR w3 ∧ RunsTo (synthesizeFromConst … (entryConst true false [] ci …)) … w3 (M,D) w4 ∧ RunsTo (coreFinally …) … w4 () w'` | **Exists** (law-free) | — |
| S5 | the reads of one core run with `ci/envR/envR'/shape` and the gate/shape facts | `Tools.ShippingGen5RunReads.runReads_of_run` [T] `Tools/ShippingGen5RunReads.lean:181` (`RunReadsAt` structure above it) | `(hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) (hr : RunsTo (synthesizeCombinationalCore X [] false) … w (raw,D) w') (entry : MachineDefines … X shape) (closes : MachineClosesAtA O mctx cctx X shape) : ∃ b ci envR envR' w5 w6, RunReadsAt … ∧ JQC O (D₀+1) w5` | **Exists** (DG-RUNREADS done). Premises left: `MachineDefines`, `MachineClosesAtA` (= the per-declaration content of `ReflectsAll`, M4) and `JQ` at `w` from `Start` (`Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`; the passage `JQC 0 ⇒ JQ 0` has not been checked in this survey) | DG-RUNREADS (done) |
| S6 | `ReadsAt env₀ cref w` at the start world | `readsAt_self` [T] `Tools/ShippingGen5Env.lean:36` | `ReadsAt (envAt cref w) cref w` | **Exists** at `w` itself | — |
| S7 | `ReadsAt env₀ cref w1` after `coreHead` (needed by `ci_of_readsAt` to get `env₀.find? X = some ci` from the run's `getConstInfo`) | `ReadsAt.of_frame` (E3) needs `EnvFrame coreHead …` | `EnvFrame` for `coreHead` / `GetEnvFrame`: this survey found no theorem (`EnvFrame.pure/bind`, `envFrame_getConstInfo` need `GetEnvFrame`; `getEnvFrame_of_readKeeps` needs `ReadKeeps`, not derived from `Start`) | **Unsupplied / this survey found no route** (= DG-ENV C0 for later worlds; `hall` appears as a premise in `machineDefines_of_readsAll`) | `sparkle-gen5-dg-env` (doing) |
| S8 | reader run ⇒ `ReadRoot` and `ReadFields` for ONE `ci/env/w1/w2` | `readMachine_root` [r10] (`ReadKindsU6`), `readMachine_fields` [r10] (`ReadKindsU7`); the one-tuple join `readMachine_rootFields` and `readMachine_gates`, `machineDefines_of_readMachine` are **U8 design [r11], no Lean yet** | `h : RunsTo (readMachine declName allowGate) … w r w' → ∃ ci env w1 w2, RunsTo getEnv … w env w1 ∧ RunsTo (getConstInfo declName) … w1 ci w2 ∧ ReadRoot ci env r` (resp. `ReadConcl ci env r ∧ ReadFields ci env r`) | root/fields **Exist** [r10] (built, scoped approved per the brief); U8 in implementation (g5rk-r12) | `sparkle-gen5-dg-readkinds` |
| S9 | tie of the reader run `readMachine declName` to the core run of the SAME declaration (`hX : declName = X`, same `ci/env`) | none | U8 §4: "This survey found no theorem relating the two runs"; `RunReadsAt` carries its own `machineShape?` fact for the core run, `ReadConcl` is about the separate reader run | **Unsupplied / this survey found no route** (real-run tie) | `sparkle-gen5-dg-readkinds` (stated in U8 §4/§8); not re-surveyed here |
| S10 | `GP env₀ declName = some p` (O2), package fields `p.d/p.decl/kD` | DG-ACC `genP`, `genP_generated`, DG-SEM `genSem_d/decl`, DG-DATAOF `dataOf_sound` | per `DC_CONNECT_FREEZE.md` §C.5/§C.7 | **Waits** (freeze only / in progress) | `sparkle-gen5-dg-acc`, `-dg-sem`, `-dg-dataof` (all doing); `-dg-cover` |
| S11 | `Acc (CallRel K) X` for the entry | DG-ACC `acc_of_run` | freeze only | **Waits** | `sparkle-gen5-dg-acc` |
| S12 | `ConstValueRel` rows 0, 3, 5 (`∃ α v, CV env₀ X α v`, quote/eval agreement per node kind, calls) and `ConstValueFunctional (ConstValueE …)` | `ConstValueE` (DCF) | not written; `DC_CONNECT_PRIM_TABLE_DECISION.md` records the table question | **Unsupplied / this survey found no route**; rule design for rows 3 is the open DCF unit | this Issue (DCF unit, own freeze) |
| S13 | `TgtRun ⊆ Reach` (G-REACH), `Tgt X ⇒ P X = some p` (`genP_pkg`) | `T1Hyp.closed`; DG-PKGASSIGN | unsupplied / waits | — | `sparkle-gen5-dg-acc` (PKGASSIGN), T1 (gen3) |
| S14 | `ReflectsAll L declName parameters` | none in Lean (`git grep` on the surveyed base finds `.md` text only) | `ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop`, "fixed in M4" | **Unsupplied in the surveyed base** (this survey found no Lean definition) | `sparkle-gen4-fg-assembly` for the final adoption; per-declaration content via `sparkle-gen5-reader-bridge` (`MachineDefines`/`GateDefines` only) and the route Issues `sparkle-gen4-gate-supply`, `sparkle-gen4-fallback-supply`, `sparkle-gen4-parametric-supply` |

## 3. Which rows close from existing approved parts
- **O1 on the DEFAULT route, for `Post := the T1Stmt relation`:** the core run and the module `raw` exist (S1/S4). What is missing is only the `mergeChecked` form of S1's last disjunct. Both are existing, law-free facts about the compiler text: the proof of `synthesizeCombinational_reads` already has `M' = mergeChecked (dropZeroWidthModule M)` before it applies `mergeChecked_cases`. This is closable by a NEW lemma in a new file with no dependency on any in-flight owner.
- DeclConnect rows 1 (unfolding), 2 (shape/body), 4 (`X.machine_source`) and 5 (calls): **do not close** from existing parts (S7, S8-S12 above). Not claimed.
- O2/O3/NV: depend on S10-S14. Not claimed.

## 4. The first unit and why (U-POST)
**Why this one:** it is the only row whose inputs are all existing approved text (S1, S2, `mergeChecked`), it does not overlap any Issue in flight (S7-S12 belong to dg-env / dg-readkinds / dg-acc / dg-sem / dg-dataof / DCF), and its core-run output is the input every later row (S4, S5) needs from the `EntryWitness`. It supplies a real fragment of O1 and is therefore also the first non-parameter link between `FG_CONNECT` and the actual entry. It does not choose `Post`: it states the relation `PostT1` and proves that the actual default entry satisfies it.

New files only: `Tools/ShippingGen5DCEntry.lean` (namespace `Tools.ShippingGen5DCEntry`), `Tests/Gen5/DCEntryCheck.lean`, `lean_lib` additions in `lakefile.lean`. `open Tools.ShippingEntrySoundness (RunsTo)`, `Sparkle.IR.ZeroWidth`, `Sparkle.IR.RefineCheck`. Fully explicit binders (as in `synthesizeCombinational_reads`).
```lean
/-- the post-processing relation of the default entry, the text of `T1Stmt`'s hypothesis (Tools/ShippingGen2Defs.lean:362-364) -/
def PostT1 (b raw : Sparkle.IR.AST.Module) : Prop :=
  b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)

theorem synthesizeCombinational_postT1 {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w') :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostT1 b raw

/-- O1 of `FG_CONNECT` on the default route, at `Post := PostT1`: the first component, for any `EntryWitness` whose route disjunct is the left one -/
theorem o1_default {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w') :
    ∃ raw, PostT1 b raw
```
`o1_default` has no `ReflectsAll` / `Laws` / `parameters` binder (they were unused; they are part of `EntryWitness`, not of this fragment).
**Relation of D and D′ (explicitly NOT provided).** `synthesizeCombinational_postT1` returns the design `D′` of the run and the core's `D` only as an existentially bound variable inside the core-run conjunct; it states NO relation between `D` and `D′` (`synthesizeCombinationalWith` rewrites the top module of `D` by `top …`). `o1_default` forgets `D` altogether. **O3 quantifies over an arbitrary `raw`** (`∀ raw, Post b raw → …`), so `PostT1`'s `∃ raw` does not by itself connect to the `raw` of the real core run. Two obligations are therefore separate and UNSUPPLIED by this unit: (i) the transport of `TopShips`' design `D` to the returned `D′` (design transport), and (ii) the connection from the arbitrary `raw` of O3 to the `raw` of the actual core witness (a uniqueness/determinism of `raw` given `b`, or a restated O3). This survey found no supplier for either.

Not claimed by this unit: the parametric route (S3), that M4 adopts `PostT1` as `Post`, O2, O3, DeclConnect, any real `ReflectsAll`, NV-witness. `o1_default` is conditional in the sense that `FG_CONNECT`'s `Post` is M4's parameter; with `Post := PostT1` it is unconditional for the default route.

## 5. Check plan (`Tests/Gen5/DCEntryCheck.lean`; counts reported with category and counting rule)
- **TYPE:** `ExpPostT1`, `ExpPostRun`, `ExpO1` written from §4's prose here (not copied from the Lean), compared with the same reducible comparator `Tests.Gen3.ExpectedType.checkExpected`; positive control (the comparator accepts a copy). Counted per statement (3).
- **MUTANT** (well-typed, ONE change, rejected by the same comparator; signature/defeq rejections, NOT semantic counterexamples): `mergeChecked`→`mergeDuplicates` (this is exactly the form of `synthesizeCombinational_reads`); the `PostT1` disjunct dropped (only `drop` kept); the core-run conjunct dropped; `∃ raw` replaced by `∀ raw`; the core run with `parameters`-style arguments (`[] false` changed); `PostT1 b raw` argument order swapped; for `o1_default` the premise route replaced by `synthesizeCombinationalWithParameters` (changes the claim to a route this unit does not prove). A mutant that is not well-typed is NOT counted.
- **Conjunction-drop mutants (`o1_default` has the binder list exactly as in §4; the expected statement is written without `ReflectsAll`/`L`/`parameters`):** conclusion's conjunct dropped (core run / `PostT1`), counted separately as category "CONJ".
- **CLOSURE:** value-closure walk of the three declarations (reused collector `DeclConnectCheck` walk: unknown name = FAIL, with its three negative controls); owner constants named explicitly (`synthesizeCombinational`, `synthesizeCombinationalCore`, `mergeChecked`, `dropZeroWidthModule`, `RunsTo`); core/opaque boundaries are leaves and are reported.
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`.
- STATUS line lists the NOT supplied rows S3, S7, S9-S14.

## 6. Next units after U-POST (order only; each needs its own freeze text before Lean)
1. `entryWitness_core` : `EntryWitness` with the left route ⇒ `Start L mctx cctx w ∧ ∃ raw D w1, core run ∧ PostT1 b raw`, then S4 (`core_chain`) to expose `ci/envR` — pure assembly.
2. The `JQC 0 ⇒ JQ 0` passage from `Start` to feed `runReads_of_run` (S5): to be checked in the freeze of unit 2 (not examined here).
3. Everything involving S7-S14 waits on the owners listed; this Issue does not re-implement them. The DCF unit (S12) keeps its own freeze.

## 7. Not claimed
D/D′ design transport, arbitrary-`raw` (O3) to core-witness `raw` connection, O2, O3, DeclConnect rows, parametric route, `ReflectsAll`, `Post` adoption by M4, NV-witness, `hall`/C0, real-run tie, DCF, FG completion, M5. The Issue stays open.
