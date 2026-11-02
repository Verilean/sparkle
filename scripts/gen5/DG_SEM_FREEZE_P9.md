# DG-SEM freeze P9 — next unit U9 `DataOfSound` ⇄ (3-conjunct soundness + `initOk_of_ok`) (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated in this commit.** Agent g5sm-u22, base `d0a8cf66` (P8 / U8 approved, build `smu21v-d0a8cf66` exit 0, 719 jobs: VALUE 3 / TYPE 5 / MUTANT 25 / AXIOMS 9). Header sync of `Tools/ShippingGen5SemGenData.lean` and `Tests/Gen5/GenDataCheck.lean` to that build (defeq-only sites noted: `hunf_of_genData` binder 10 `hinv` and conclusion; `factsOf_all_of_genDataInv` binder 10 `hinv`) is commit `1ccf0f9d` (comment only, no rebuild).
Everything below is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean` untouched), no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree; `[br:X@sha]` = another branch (NOT in this tree, not an ancestor; merging is out of scope); `[N]` = new here.
Method: names and statement heads read with `git show` / `grep` / `Read`; nothing elaborated. "この調査で辿った候補経路では未供給" does not claim impossible.

## 1. Survey: which rows of the real supply close from existing names

Rows still open after U8: `DataOfSound dataOf initsOf` for the real `dataOf`; the kit rows `hsem / hd / hmem / hinv` for a real `AssignKit`; a `GenData` value (needs `GenWF`); run; FG.

| row | existing name (full statement head) | where | status for DG-SEM |
|---|---|---|---|
| `DataOfSound (dataOfAt lvl) initsOf`, conjuncts 1–3 | `dataOfCore_sound (lvl) {shape} {nIn} {dom} {d} (h : dataOfCore lvl shape nIn dom = some d) : d.shape = shape ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed` | `[br:g5do-r6 Tools/ShippingGen5DataOf.lean]` | DG-DATAOF owns; not importable |
| conjunct 4 | `initOk_of_ok (d : MachineData) (h : d.ok = true) : d.initOk (initsOf d) = true` (`initsOf d := initsFrom d.shape.layout.slots d.ss`) | `[br:g5do-r6 Tools/ShippingGen5DataOfPure.lean:412]` | DG-DATAOF owns; not importable |
| all 4 for `dataOfAt` | `dataOfAt_sound (lvl) {E} {senv} {s} {d} (h : dataOfAt lvl E senv s = some d) : d.shape = s ∧ d.ok = true ∧ d.shape.body = quote … d.packed ∧ d.initOk (initsOf d) = true` | `[br:g5do-r6 Tools/ShippingGen5DataOf.lean:211]` | at integration `DataOfSound (dataOfAt lvl) initsOf` is `fun E senv s d h => dataOfAt_sound lvl h`; not buildable here (file absent) |
| 3-conjunct form | `DataSoundAt f : Prop := ∀ E se s d, f E se s = some d → d.shape = s ∧ d.ok = true ∧ d.shape.body = quote …` ; `dataSound_of_agree K f hf hK : DataSound K`; `DataSound K` is the same 3 conjuncts for `K.dataOf` | `[br:g5ac-r26 Tools/ShippingGen5AccDataAgree.lean, …AccDataSound.lean]` | DG-ACC owns. **Shape gap**: DG-ACC's statements have 3 conjuncts, DG-SEM's `DataOfSound` has 4 (adds `initOk`). |
| `hmem` | `ordCallees₀_mem (d) (k) : k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? = none`; field `AssignKit.mem_ordCallees` | `[br:g5ac-r26 Tools/ShippingGen5AccOrdCallees.lean, Acc.lean]` | DG-ACC; named only |
| `hinv` | `genS_some_inv K`, `callEdge_of_ord K hE hg` | `[br:g5ac-r26]` | DG-ACC; named only |
| kit `dataOf` ← real | `mkKit …`, `GDEvidence f GD dOf env₀`, `KitAgrees K f` | `[br:g5ac-r26 …AccMkKit.lean, …AccGenDataEv.lean]` | DG-ACC; named only |
| `dataOf` at `exprSize`, coverage (`dataOfAt … = some _` on a run), `GenWF` for a run | DG-DATAOF §11.2 rows 1–6, 8 (`mixedGatePeel`, `readN`, `splitLets`, `typedFields`, `d.ok`); `genWF_iff` | `[br:g5do-r6 scripts/gen5/DG_DATAOF_FREEZE.md §11]`, `[br:g5cv-r13]` | DG-DATAOF / DG-COVER / readertrace; この調査で辿った候補経路では未供給 |

**Finding.** The one row that is DG-SEM's and buildable here is the *shape gap* above: P8's `DataOfSound` has four conjuncts; the real suppliers give three (`dataOfCore_sound`-shaped, DG-ACC's `DataSoundAt`/`DataSound`) plus a separate `initOk_of_ok : d.ok = true → d.initOk (initsOf d) = true`. Nothing in this tree says `DataOfSound ⇔ (3 conjuncts) ∧ (initOk from ok)`; that is a pure-logic fact over `MachineData` that needs only the P8 definition. Stating it as theorems makes integration `dataOfSound_of_parts` (premises = the two real lemmas' statements verbatim) instead of an unchecked "dataOfAt_sound-shaped" remark, and lets a `DataSound K` (DG-ACC) be consumed as `DataOfSound` with `initOk_of_ok`. The remaining rows (real `dataOf`/coverage/`GenWF`, real kit, run, FG) are not DG-SEM's or do not close from names; **この調査で辿った候補経路では未供給**.

## 2. First unit and why: U9 = `dataOfSound_of_parts` / `dataOfSound_parts`
Reasons: (1) it closes entirely from the P8 definition (new file only, depends on `Tools.ShippingGen5SemGenData`); (2) it is the only candidate row found that needs neither `[br:…]` imports nor a law; (3) it is the exact interface for the integration step (`hf := dataOfCore_sound`-shaped, `hinit := initOk_of_ok`); (4) no `GenData` value, no run.

### 2.1 Complete types
New file `Tools/ShippingGen5SemDataOfParts.lean`, `namespace Tools.ShippingGen5Sem`, `set_option autoImplicit false`, `import Tools.ShippingGen5SemGenData`, same `open`s as `Tools/ShippingGen5SemGenData.lean`. Lakefile: one `lean_lib` for it, one for its Check.

```lean
theorem dataOfSound_of_parts
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = true) :
    DataOfSound dataOf initsOf :=
  fun E senv s d h =>
    ⟨(hf E senv s d h).1, (hf E senv s d h).2.1, (hf E senv s d h).2.2, hinit d (hf E senv s d h).2.1⟩

theorem dataOfSound_parts
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true) :=
  ⟨fun E senv s d h => ⟨(hs E senv s d h).1, (hs E senv s d h).2.1, (hs E senv s d h).2.2.1⟩,
   fun E senv s d h => (hs E senv s d h).2.2.2⟩
```
(`ι`, `dom` unused here; `quote`/`inputExpr` as in the P8 file.) Proofs are term-mode projections/tuples; if a `quote` elaboration issue appears the fallback is `by intro …; exact …`, not a change of statement.

### 2.2 Check plan (same requirements as U8)
New `Tests/Gen5/DataOfPartsCheck.lean`, `import Tools.ShippingGen5SemDataOfParts`, `import Tests.Gen5.GenDataCheck`, reuses `checkExpected`/`cmpTele`/`checkValue`.
* THEOREMS (2): type against independent `ExpDataOfSoundOfParts`, `ExpDataOfSoundParts` written separately in the Check; `Expr.eqv` first; any defeq-only binder/conclusion is **reported** (not silently passed), counted separately.
* No new `def`/`structure` ⇒ no VALUE/telescope part for U9; U8's `DataOfSound` value stays covered by `GenDataCheck`.
* MUTANT (well-typed single changes, rejected by signature/defeq comparison — **not semantic counterexamples**): drop `hinit`; `hinit` with `d.ok = false`; `hf` with `d.ok = false`; `hf` dropping the `d.shape = s` conjunct; result `DataOfSound` swapped for the `dataOf`/`initsOf`-permuted instance; `_parts` conclusion 2 using `d.initOk (initsOf d) = false`; `_parts` conclusion 1 with conjuncts reordered. Count = what actually elaborates and is rejected, reported as measured.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`); sorry-free; CLOSURE with positive controls (root itself judged, `DataOfSound` reached), negative controls (an unknown helper constant by value and by type is flagged); REACH.
* Clean build is the coder's; Pod increment `kjob lake build Tools.ShippingGen5SemDataOfParts` then `Tests.Gen5.DataOfPartsCheck`.

## 3. Not supplied after U9 (unchanged)
Real `dataOf`/`initsOf`/`DataOfSound` for the compiler (DG-DATAOF: `dataOfAt_sound`, `initOk_of_ok`, coverage rows 1–6, 8); `GenWF` for a run (DG-COVER); real kit `hmem`/`hinv`/`mkKit` (DG-ACC); readertrace; `GenData` values; run; FG. This is not a DG-SEM / M5 / FG completion.
## 4. Decision needed?
No: no new law/TRUSTED, no shared-definition edit, no scope reduction.
