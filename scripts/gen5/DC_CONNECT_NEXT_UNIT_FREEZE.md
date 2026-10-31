# DC-CONNECT next unit: freeze of U-ENTRYW (agent g5dc-r14, base `kjob/g5dc-r13` 6d6c9b22 = U-TOPNAME approved, build dc13v-6d6c9b22 exit 0, 749 jobs)
**Design only; no Lean in this commit.** "Unsupplied / this survey found no route" is a statement about THIS survey (this tree; `par/gen5-t2`; `kjob/g5rk-r12..r14`; `kjob/g4fb-*` by name only), not impossibility. A "mutant" is a signature/defeq rejection of a well-typed changed statement, not a semantic counterexample. No new law/TRUSTED, no shared-definition/compiler edit, FG not narrowed, `GenWF` not strengthened, no `Post` adoption.

## 1. Synchronisation and sharing (done / recorded)
- Headers of `Tools/ShippingGen5DCEntryN.lean` and `Tests/Gen5/DCEntryNCheck.lean` now state build dc13v-6d6c9b22 (approved at 6d6c9b22; comment-only commit 75f89c9e). Survey §13-§16 (addendum 2) tables describe the pre-implementation state of U-TOPNAME; rows (a2.1)-(a2.3) are now **supplied** by the seven approved theorems (types in survey §13); (a2.4), (a3), (b1), (b2), (c4 import), (c5), (c6), (c7) are unchanged below.
- Observation for the reviewer: the header commit 6d6c9b22 removed the line `set_option autoImplicit false` from `Tools/ShippingGen5DCEntryN.lean` (the approved build dc13v-6d6c9b22 is of that tree, so the build does not depend on it). It was NOT restored here because restoring is a non-comment change that would need a rebuild; whether to restore it is for a later Lean-touching commit.
- Sharing with FB-15 (`sparkle-gen4-fallback-supply`, own-name lookup): `moduleByName_topMap_self` and the helper `find_map_self` duplicate FB-15's own-name lookup. On integration, FB-15's lemma is to be reused from here (these are the existing supply); nothing is changed in this Issue for that. I did not read the `kjob/g4fb-*` sources for this note beyond the branch names, so the exact FB-15 statement is NOT recorded here.

## 2. Remaining rows, and what closes from existing lemmas (real names, full types)
| row | route searched | status |
|---|---|---|
| (c1′) `EntryWitness` ⇒ `Start` ∧ (default-route core run with `PostEntry` ∨ the `WithParameters` run) | `EntryWitness` (`Tools/ShippingGen5FG.lean:32`), `Start` (`Tools/ShippingGen2Defs.lean:52`), `synthesizeCombinational_postEntry` (`Tools/ShippingGen5DCEntryD.lean:28`) | **closable now** by case split on the route disjunct and the approved theorem; chosen as U-ENTRYW below |
| (a2.4) `ResetNk`/`childMap` run transport `D → D′` | needs the premise "no descendant module is named `raw.name`"; survey §12 found no supplier | unsupplied / this survey found no route to the premise. A conditional lemma taking the premise as a hypothesis is possible but is a candidate AFTER U-ENTRYW and is not frozen here |
| (a3) post-processed top semantics | as survey §8 (a3) | unsupplied / no route found |
| (b1) arbitrary `raw′` with `PostT1 b raw′` | no injectivity/determinism theorem for `dropZeroWidthModule`/`mergeChecked` found | unsupplied / this survey found no route; not claimed either way |
| (b2) restate O3 | changes the stated `FG_CONNECT` guarantee | reviewer/user decision (survey §8 (b2)); NOT opened here |
| (c4) `readMachine_rootFields` | exists on `kjob/g5rk-r12..r14`, not in this tree | import needs a merge/dependency decision outside this Issue |
| (c5) reader/core tie; (c6) `hall`/later-world `ReadsAt`; (c7) O2/DC rows, ConstValue | owners dg-acc / dg-sem / dg-dataof / DG-ENV | unsupplied / this survey found no route in Lean; waits |
| right route (`synthesizeCombinationalWithParameters`) postprocessing | no `PostEntry`-style lemma for it in this tree (S3) | unsupplied; U-ENTRYW keeps it as an explicit disjunct, not claimed |

No row here needs a new law, TRUSTED boundary or shared-definition change, so no decision document is required.

## 3. The unit to implement first: U-ENTRYW, and why
**Why:** it is the only remaining row whose every input is existing approved text, and it is the first statement phrased on the actual `EntryWitness` (so far the chain U-POSTD/U-TOPNAME is about bare `RunsTo` hypotheses). It consumes no `ReflectsAll` content and does not supply an `EntryWitness`; it only reads one. It does not close D→D′ transport, O3, DeclConnect or FG.

New files only: `Tools/ShippingGen5DCEntryW.lean` (namespace `Tools.ShippingGen5DCEntryW`; `import Tools.ShippingGen5FG`, `import Tools.ShippingGen5DCEntryD`; `set_option autoImplicit false`), `Tests/Gen5/DCEntryWCheck.lean`, `lean_lib` additions in `lakefile.lean`. `open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG` as needed; `open Tools.ShippingEntrySoundness (RunsTo)`; `open Tools.ShippingGen5DCEntryD (PostEntry)`. Fully explicit names, binders as in `EntryWitness`.
```lean
theorem entryWitness_postEntry {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D') :
    Start L mctx cctx w ∧
    ((∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
        RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

theorem entryWitness_left_postEntry {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w') :
    Start L mctx cctx w ∧
    ∃ (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'
```
Proof route: `obtain ⟨hS, hr, -⟩ := h`; `rcases hr with hr | hr`; left: `synthesizeCombinational_postEntry hr`; right: keep. The second theorem is the first applied with `hl` (no case split needed: `⟨h.1, synthesizeCombinational_postEntry hl⟩`; `h` is used only for `Start`). If a proof does not go through as stated, the statement is NOT changed (stop and report). Note: the types are fixed from `EntryWitness`' definition as read at `Tools/ShippingGen5FG.lean:32-40`; the final design variable is called `D'` in the statements (it is `D` in `EntryWitness`' own binder list).

## 4. Check plan (`Tests/Gen5/DCEntryWCheck.lean`; same requirements as U-TOPNAME)
- **TYPE:** independent `Exp*` for both theorems written from the prose of §3 (not copied from the Lean), compared with `Tests.Gen3.ExpectedType.checkExpected` under `withReducible`; self-comparison positive control not counted.
- **MUTANT** (well-typed single change only; signature/defeq rejection, NOT semantic counterexamples; a mutant that is not well-typed is NOT counted): `Start` conjunct dropped; `PostEntry b raw D D'` replaced by `PostEntry b raw D' D`; `∨` → `∧` in the first theorem; the `WithParameters` run's `parameters` replaced by `[]`; the core run's `[]`/`false` arguments changed to `parameters`/`true` (only if well-typed); `hl` stated with `synthesizeCombinationalWithParameters`; `w'` replaced by `w` in the route.
- **CONJ:** each conjunct of the second theorem's conclusion dropped, counted separately; each disjunct of the first dropped, counted separately.
- **CLOSURE:** the `DeclConnectCheck` walker: root judged itself, unknown name = FAIL; positive and negative controls (a root with an unreached required name is detected; one with the extra name is clean); an unknown-name fixture whose helper's TYPE alone mentions an unknown name; intended name asserted; `withoutModifyingEnv`; afterwards the CURRENT environment (`getEnv`) is inspected for leak. Required names per root: `EntryWitness`, `PostEntry`, `synthesizeCombinational_postEntry`.
- **AXIOMS:** `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`; counts reported as measured with category and counting rule after the build of the committed tree. Builds are the coder's (clean issue-linked); an agent incremental build, if run, is labelled NOT clean.
- STATUS line lists the NOT supplied rows: (a2.4), (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), right-route post-processing, `ReflectsAll`, real `EntryWitness`.

## 5. Not claimed
Supplying an `EntryWitness` or `ReflectsAll`; D→D′ transport of `TopShips`/`ResetNk`; O3 arbitrary-`raw` identification; post-processing of the parametrised route; `Post` adoption; FG completion; M5. The Issue stays open.

## 6. Implementation record (agent g5dc-r15) and FB-15 comparison
- Implemented exactly the two §3 statements (no statement change, no extra hypothesis) in `Tools/ShippingGen5DCEntryW.lean`, checked by `Tests/Gen5/DCEntryWCheck.lean`; `set_option autoImplicit false` present in both and both build with it. Built files, shared definitions and the compiler are untouched. `Tools/ShippingGen5DCEntryN.lean` still lacks `set_option autoImplicit false` (removed by 6d6c9b22); it is a built file and was not edited here.
- FB-15 comparison (read from `kjob/g4fb-fb16:Tools/ShippingGen4FbPPLookup.lean`, exact types): `moduleByName_map_self (N : String) (f) (hf : ∀ x, (f x).name = x.name) : ∀ l x, moduleByName l N = some x → moduleByName (l.map fun y => if y.name == N then f y else y) N = some (f x)` is the `some`-premise form (needs the lookup to succeed). Here `moduleByName_topMap_self (hf) : moduleByName (topMap f m d).modules m.name = (moduleByName d.modules m.name).map f` has no success premise and is stated on `topMap`; the FB-15 form follows from it by rewriting the premise. `ppRel_lookup_self`/`ppRel_lookup_other` are stated on FB-15's `PPRel`, which is not `PostEntry`; whether they coincide with `PostEntry`-based statements is not decided here. Nothing duplicated or removed; integration to reconcile.
- Agent build (NOT a clean issue-linked build): `kjob lake build Tests.Gen5.DCEntryWCheck` exit 0, 751 jobs on the tree to be committed. Counts: TYPE 2 (+2 self-comparison positive controls not counted), MUTANT 12 (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), CONJ 8 (conjunct/disjunct drops incl. `Start`-drop, counted once), AXIOMS 2 standard only, CLOSURE 2 roots + 1 missing-requirement + 1 forbidden-mention + 1 clean control + unknown-name fixtures (type-only, value-only detect; 1 clean). No sorry.

## 7. Synchronisation after approval (agent g5dc-r16, comment/docs only; no rebuild)
- U-ENTRYW approved at 135aa0ac (build dc15v-135aa0ac exit 0, 751 jobs, dirty=false); headers of `Tools/ShippingGen5DCEntryW.lean` and `Tests/Gen5/DCEntryWCheck.lean` now say so. Scoped approval: the two theorems only; not the Issue, not M5.
- TYPE: the build log's "TYPE OK 4" has 2 distinct theorem comparisons; the other 2 lines are repeated/self comparisons. Distinct = 2. MUTANT 12 + CONJ 8, AXIOMS 2 standard only.
- "Single change" made concrete: `MutW2Forall` changes all three existential quantifiers (`∃ raw D w1`) to `∀` as one block; `MutW1CoreArgs` and `MutW2Flag` change two arguments (`[]`/`false` → `parameters`/`true`) of the core run together. The other mutants change one component. All are signature/defeq rejections under `withReducible`, not semantic counterexamples.
- `set_option autoImplicit false` was verified in `Tools/ShippingGen5DCEntryW.lean` and `Tests/Gen5/DCEntryWCheck.lean` only; `Tools/ShippingGen5DCEntryN.lean` is NOT restored (as §1).
- Kept unsupplied: real `EntryWitness`, `ReflectsAll`, D→D′ transport, O3, `Post`, FG. FB-15 reuse comparison is at integration.
