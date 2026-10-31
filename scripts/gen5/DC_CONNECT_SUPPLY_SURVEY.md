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

---
# Addendum (agent g5dc-r10, base `kjob/g5dc-r9` db171c2e, U-POST approved): D′ transport, O3 witness identification, real EntryWitness — survey + freeze of the next unit
**Design only; no Lean in this commit.** Wording as in the head of this file: "unsupplied / this survey found no route" is a statement about THIS survey (this tree, `kjob/g5rk-r12..r14`, `par/gen5-t2`), not impossibility. A "mutant" is a signature/defeq rejection of a well-typed changed statement, not a semantic counterexample. `FG_COND`/`FG_CONNECT` stay conditional; U-POST is not an adoption of `Post`. No new law/TRUSTED, no shared-definition/compiler edit, FG not narrowed, `GenWF` not strengthened.

## 8. The three rows (read from `Tools/ShippingGen5FG.lean`, `Tools/ShippingGen2Defs.lean`, `Sparkle/Compiler/Elab.lean:5592-5606`)
Key fact read from the sources: `T1Stmt` / `StepStmt` / `MemParentStmt` / `LeafStmt` state `TopShips p n c b raw D` with `D` the design of the **core** run (`RunsTo (synthesizeCombinationalCore c [] false) … (raw, D)`), but `FG_CONNECT` O3 states `TopShips p n declName b raw D` with `D` the design of the **entry** `EntryWitness … b D` (`RunsTo (synthesizeCombinational declName) … (b, D)`), i.e. the RETURNED design D′. `synthesizeCombinationalWith` builds it as `D′ = top mergeChecked (top dropZeroWidthModule D)` (or `top dropZeroWidthModule D` when `SPARKLE_NO_REGDEDUP` is set) with `top f d := { d with modules := d.modules.map fun x => if x.name == m.name then f x else x }`, `m` = the core's module.

### Row (a): transport to the returned design D′
| step | name and full type | status |
|---|---|---|
| (a1) relation of D and D′ as a statement about the compiler text | none exists (`synthesizeCombinational_reads`, `…_postT1` return `D` only inside the core-run conjunct) | **NEW lemma `synthesizeCombinational_postEntry` below**: closable by the same unfolding as U-POST (`RunsTo.bind`, `RunsTo.ite`, `RunsTo.pure`); no law |
| (a2) `TopShips p n c b raw D → TopShips p n c b raw D′` | `TopShips` (`Tools/ShippingGen2Defs.lean:280`) uses `D` only in `ResetNk n raw D kids` and `childMap D.modules` (and `KSn (childMap D.modules) n`) | **Unsupplied / this survey found no route.** It needs: the changed module (`x.name == raw.name`) is not looked up as a child (`childMap` lookups of other names are unchanged by `top`, but a child named `raw.name`, or a second module with that name, is not excluded by anything read), and `ResetNk` invariance. This survey did not find a theorem about `childMap (D.modules.map …)`, `ResetNk` under `top`, or name-distinctness of `D.modules` from the core run. Not claimed. |
| (a3) the post-processing of the top module inside `D′` preserves the semantics `TopShips` observes (`checkedOptimize b`) | `postprocess_sound`, `postprocess_facts` (`Tools/ShippingPostSoundness.lean:551,737`) are about the module, with side conditions (`0 < n`, nodup wires) | **Unsupplied for the design-level statement / this survey found no route**; not examined beyond the names |

### Row (b): O3's arbitrary `raw` versus the core witness's `raw`
O3 is `∀ raw, Post b raw → ∃ p n, GP … = some p ∧ TopShips p n declName b raw D`. For `Post := PostT1` the `raw` is any module with `b = drop raw ∨ b = mergeChecked (drop raw)`.
| step | name and full type | status |
|---|---|---|
| (b1) identify an arbitrary `raw′` with `PostT1 b raw′` with the `raw` of the core run | needs `dropZeroWidthModule` (and `mergeChecked ∘ drop`) injective on the relevant modules | **Unsupplied / this survey found no route.** `dropZeroWidthModule` (`Sparkle/IR/ZeroWidth.lean:113`) is a function that returns `m` unchanged or rewrites it; no injectivity theorem was found; whether it is injective is not decided here. `runsTo_det` (`Tools.ShippingStRefCorrespondence.runsTo_det`, restated as `Tools.ShippingGen5ReadKindsU8.runsTo_det` [r12-r14]) gives uniqueness only among runs of the SAME computation from the same world, which does not apply to an unrelated `raw′`. |
| (b2) restate O3 so that the `raw` is the witness's | requires a change of the `FG_CONNECT` statement (`Post` is `Module → Module → Prop` and cannot mention the world `w`) | **Not done: it changes the stated guarantee and is a user/reviewer decision, not made here.** If (b1) is unavailable, the alternative is a `Post` that is strong enough that `Post b raw′` forces the identification (M4's choice: `sparkle-gen4-fg-assembly`). |

### Row (c): the real EntryWitness (what is needed to derive O1/O2/O3/DC for ANY witness)
| step | name and full type | status |
|---|---|---|
| (c1) route disjunct ⇒ core run + post relation | U-POST `Tools.ShippingGen5DCEntry.synthesizeCombinational_postT1` (approved) | **Exists** for the left (default) route; the right disjunct (`synthesizeCombinationalWithParameters`): no Lean in the surveyed trees (S3) |
| (c2) core run ⇒ linked chain | `Tools.ShippingEntryReadsLinked.core_chain` | **Exists** |
| (c3) chain ⇒ reads of the run | `Tools.ShippingGen5RunReads.runReads_of_run` (premises `JQ O.quiet D₀ w`, `D₀ = 0 ∨ CacheInvA O (cv w)`, `MachineDefines`, `MachineClosesAtA`) | **Exists**; premises: `JQ` from `Start` (`Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`; `JQC 0 ⇒ JQ 0` not examined), `MachineDefines`/`MachineClosesAtA` = content of `ReflectsAll` (S14, M4) |
| (c4) reader run ⇒ `ReadRoot ∧ ReadFields` for ONE `ci/env/w1/w2` | `Tools.ShippingGen5ReadKindsU8.readMachine_rootFields` [r12-r14, clean build rk12v-f86cbdd7]: `RunsTo (readMachine declName allowGate) … w r w' → ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) … w env w1 ∧ RunsTo (getConstInfo declName) … w1 ci w2 ∧ ReadRoot ci env r ∧ ReadFields ci env r`; also `readMachine_gates`, `machineDefines_of_readMachine` (conditional on `hall`) | **Exists on those branches, NOT in this tree** (this tree does not import it; using it needs the branch to be merged or a dependency, which this Issue does not do) |
| (c5) tie of the reader run to the core run of the same declaration | `kjob/g5rk-r14` `DG_READKINDS_U9_FREEZE.md` (U9c, `hrun` with named-world `ReadsAt`, design only) | **Unsupplied / this survey found no route in Lean** (design in flight, owner `sparkle-gen5-dg-readkinds`) |
| (c6) `hall` / `ReadsAt` at later worlds | DG-ENV C0 | **Unsupplied** (owner `sparkle-gen5-dg-env`) |
| (c7) O2 `GP … = some p`, DC (`DeclConnect`) rows | `DeclConnect` / `declConnect_eq` (`Tools/ShippingGen5DeclConnect.lean:277,281`): rows 1 (`env₀.find? X = some ci`), 2 (`shapeOf ci = some sh ∧ ShapeMatches`), 4 (`CV env₀ X sh.Ty v`), 5 (`obs = p.src`) | rows 1,2 depend on (c4)-(c6); row 4/5 on DCF (`ConstValueRel`, S12); **not closed**. FG_COND/FG_CONNECT: conditional, not FG completion. |

## 9. The first unit to implement: U-POSTD (design relation of the entry), and why
**Why:** it is the only row among (a)-(c) whose inputs are all existing approved text (the body of `synthesizeCombinationalWith`, `RunsTo.bind/ite/pure`, `mergeChecked`, `dropZeroWidthModule`) and that needs no owner (no `ReadsAt`, `hall`, `ReflectsAll`, `Post` choice). It makes the relation of D and D′ a theorem instead of an unstated gap, so (a2) becomes a precisely stated remaining obligation, and the joint form ties `b` and `D′` to the SAME branch (the separate `PostT1` gives no such tie). It does NOT close (a2), (b), (c) and does not adopt `Post`.

New files only: `Tools/ShippingGen5DCEntryD.lean` (namespace `Tools.ShippingGen5DCEntryD`, `import Tools.ShippingGen5DCEntry`), `Tests/Gen5/DCEntryDCheck.lean`, `lean_lib` additions in `lakefile.lean`. Fully explicit/`{}` binders as in U-POST.
```lean
/-- the `top` of `synthesizeCombinationalWith`: rewrite the module named like `m` -/
def topMap (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (m : Sparkle.IR.AST.Module)
    (d : Sparkle.IR.AST.Design) : Sparkle.IR.AST.Design :=
  { d with modules := d.modules.map fun x => if x.name == m.name then f x else x }

/-- module and design of the default entry, in the SAME branch -/
def PostEntry (b raw : Sparkle.IR.AST.Module) (D D' : Sparkle.IR.AST.Design) : Prop :=
  (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∧
    D' = topMap Sparkle.IR.ZeroWidth.dropZeroWidthModule raw D) ∨
  (b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ∧
    D' = topMap Sparkle.IR.RefineCheck.mergeChecked raw (topMap Sparkle.IR.ZeroWidth.dropZeroWidthModule raw D))

theorem synthesizeCombinational_postEntry {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w') :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧
      PostEntry b raw D D'

theorem postEntry_postT1 {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : PostEntry b raw D D') : Tools.ShippingGen5DCEntry.PostT1 b raw
```
Proof route: as U-POST (`unfold synthesizeCombinational synthesizeCombinationalWith at h`, `RunsTo.bind`, `RunsTo.ite`, `RunsTo.pure`, `Prod.mk.injEq`); the `top` is the `let` of the definition, so `topMap` is its `rfl`-instance; `postEntry_postT1` is `Or` case analysis. If the `rfl` of `topMap` against the zeta-reduced `top` fails, the statement is NOT changed (stop and report).
Note: `D′` here has the same `topModule` and the same module count as `D` (`{ d with modules := … }`); that is a consequence readable from `topMap`, not an added claim.

## 10. Check plan for U-POSTD (`Tests/Gen5/DCEntryDCheck.lean`; counts with category and counting rule)
- **TYPE:** `ExpTopMap`, `ExpPostEntry`, `ExpPostEntryRun`, `ExpPostEntryPostT1`, written from §9's prose (the relation: top module rewritten by name; same branch for `b` and `D′`), compared by `Tests.Gen3.ExpectedType.checkExpected` (one reducible comparator for positive and negative cases); positive self-comparison control (not counted).
- **MUTANT** (well-typed single change; signature/defeq rejection, not a semantic counterexample): `mergeChecked`→`mergeDuplicates` (needs the same type: `Module → Module`), `topMap` keyed by `x.name == m.name`→`x.name != m.name`, the inner `topMap … D` dropped in the merge branch, `D'`/`D` swapped in the relation, `∧`→`∨` between the `b` and `D′` conjuncts (joint branch dropped), core-run `[] false`→`[] true`, `PostT1 b raw` arguments swapped. Counted per mutant that type-checks; ill-typed ones are not counted.
- **CONJ:** the conclusion's conjunct dropped (core run / `PostEntry`), counted separately.
- **CLOSURE:** the `DeclConnectCheck` walker (unknown name = FAIL, root judged itself); new fixture: a helper whose TYPE mentions a name unknown to the environment (only that helper's type is unknown), the intended name asserted, `withoutModifyingEnv`; the three owner constants named (`synthesizeCombinational`, `synthesizeCombinationalCore`, `mergeChecked`, `dropZeroWidthModule`, `RunsTo`).
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`.
- STATUS line lists the NOT supplied rows: (a2), (a3), (b1), (b2), (c5), (c6), (c7), S3, S12, S14.

## 11. Not claimed (addendum)
D′ transport of `TopShips` (a2/a3), O3 arbitrary `raw` identification (b), real `EntryWitness`, `hall`, reader/core tie, O2, DeclConnect rows, `ReflectsAll`, parametric route, `Post` adoption by M4, `Post`/O3 restatement, FG completion, M5. The Issue stays open.
