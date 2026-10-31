# DG-COVER freeze rev6 — unit U-E2: row 6a (ShapeAgree, state-side half), fuel model only (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — docs only. No Lean file was edited or elaborated for this document; the Lean text below is an unelaborated proposal written against definitions read in this tree.**
Base `8e01a9cf` (kjob/g5cv-r9, U-E1 + helper 2 scoped approved), branch `kjob/g5cv-r10`. Continues `DG_COVER_FREEZE_REV5.md` (row 6a was named there as candidate U-E2).
No guarantee, law, TRUSTED boundary, FG scope or shared definition is changed or proposed to be changed; `GenWF` is not strengthened; no decision is requested.

Wording rule (as rev0–rev5): "not found" = *this investigation found no supplier or route*, never "impossible / not derivable". A mutant is a rejection of a changed statement by
signature / defeq, not a semantic counterexample. A conditional wrapper is **not** a supply. Conditional results are INTERMEDIATE.

## 0. What row 6a is, and what it is not

`ShapeAgree d st` (`Tools/ShippingGen5Cover3.lean:686`) has five fields: `insts`, `origins`, `slots : d.ss.length = st.kinds.size`, `lets : d.ls.length = st.lets.size`, `nIn : d.shape.insts.length ≤ d.nIn`.
It mixes two sides:

* **state side (row 6a, this unit)**: the facts relating the *final reader state* `st` to the `MachineShape` `sp` that `shapePost` builds from it: `sp.insts`, `sp.instOrigins`,
  `sp.layout.slots.length`, `sp.layout.lets` versus `st.insts`, `st.instOrigins`, `st.kinds.size`, `st.lets.size`.
* **`d` side (row 6b, NOT in this unit; owner DG-DATAOF)**: `d.shape = sp`, `d.ss.length`, `d.ls.length`, `d.nIn`. Projection lemmas for these were not found in the DG-DATAOF branch by the rev5 survey (this investigation found none; that is not a claim they cannot exist). Nothing of row 6b is implemented here; it enters only as explicit premises of the combination theorem T4.

**Fuel-model statement.** T1–T3 are theorems about `shapePost` and the fuel-model wrapper `Tools.ShippingReaderFuel.machineShapeF`. They say nothing about the production `machineShape?`
(`partial`-reader, opaque). The only link is `ShapeFuelBridge`: `∀ E senv sp, machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)`
(`SRC_ARGW_SUPPLY_FREEZE.md` §2, the O1/O2 boundary of this Issue, **assumed once, not proved here**). T6 states that connection with the bridge as an **explicit hypothesis** (T5 is the fuel-model step it uses); the
connection is therefore *conditional on the boundary and is not recorded as a supply of row 6a for production*. Row 6a stays "fuel model only; production only through `ShapeFuelBridge`".

## 1. Facts used (read in this tree)

* `shapePost` (`Tools/ShippingReaderFuelShape.lean:153-202`): `layout.lets := st.lets.size` (`k`), `layout.slots := machSlotFields ((kinds.map machWidth).zip st.inits.toList)` with `kinds = st.kinds.toList`,
  `insts := st.insts.toList`, `instOrigins := st.instOrigins.toList`.
* `shapePost_insts'`, `shapePost_instOrigins`, `shapePost_decomp` (`Tools/ShippingReaderFuelShapeR5.lean`); `machSlotFields_length` (`Tools/ShippingShapeDecomp.lean:121`).
* `MachRead.LenOk` (`Tools/ShippingReaderLenOk.lean:75`): `names.size = kinds.size ∧ inits.size = kinds.size ∧ instOrigins.size = insts.size`.
* `machineShapeF_steps` (all phases and states `st0 env st1 st v`), `machineShapeF_lenOk` (`st.LenOk` for every successful run).
No `st.lets.size` lemma exists under a name (rev5 §1 row 6a); T1 is that small new lemma. No new premise beyond those listed in each type.

## 2. Types (new file `Tools/ShippingGen5Cover5.lean`; unelaborated proposal)

Imports `Tools.ShippingGen5Cover3`, `Tools.ShippingReaderFuelShapeR5`, `Tools.ShippingReaderLenOk`, `Tools.ShippingShapeDecomp` (whichever are not already transitive); `namespace Tools.ShippingGen5Cover5`; `set_option autoImplicit false`;
opens as Cover4 plus `Tools.ShippingReaderFuel`. No new `def`/`structure`/`axiom`; only `theorem`s.

```lean
/-- T1 (new small lemma): sizes of the layout read off `shapePost`; no `LenOk`, so the slot count is the `min`. -/
theorem shapePost_layout_sizes {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    sp.layout.lets = st.lets.size ∧ sp.layout.slots.length = min st.kinds.size st.inits.size

/-- T2: the four state-side facts of `ShapeAgree` for the shape built from `st`, given `LenOk`. -/
theorem shapePost_state_side {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) (hL : st.LenOk) :
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

/-- T3 (fuel model): for every successful candidate run, the SAME final state `st` of that run (with the phases that produced it,
as in `machineShapeF_steps`) is `LenOk` and satisfies the four facts for the returned `sp`. -/
theorem machineShapeF_state_side {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size
```
(The first six clauses are those of `machineShapeF_steps`, repeated so that a later R-trace statement (row 1) can be attached to *this* `st`; the clause list is copied from the in-tree statement, not new content.
If the elaborated `machineShapeF_steps` differs in spelling, the Expected statement in the Check follows the in-tree one and the difference is reported, not silently adapted.)

### Combination with row 6b (T4) — the identification equations

Row 6a and row 6b are produced by **different walks**: 6a by the reader run `machineShapeF …` (state `st`, shape `sp`); 6b by `dataOf` applied to a `MachineShape` (DG-DATAOF), giving `d`.
They describe the same object only if they are about the **same `sp` and the same run**. The needed equations are therefore, for the `sp` and `st` of one T3 witness:

1. `d.shape = sp` (6b, `dataOfFrom_sound`'s `d.shape = s` instantiated at that `sp`; the `sp` must be the one T3 returned, i.e. `dataOf` applied to the run's own output — an equation, not a conjunction of two existentials);
2. `d.ss.length = sp.layout.slots.length`, `d.ls.length = sp.layout.lets` (6b projection lemmas, not found; premises here);
3. `sp.insts.length ≤ d.nIn` (6b, `d.nIn = peel.length + shape.insts.length`; premise here).

Then `ShapeAgree d st` follows by rewriting. Two unconnected facts "∃ st with 6a for some sp" and "∃ d with 6b for some sp′" must **not** be identified by conjunction: `sp = sp′` and "`st` is the final state of the run that produced `sp`" are required and are exactly premise 1 plus the shape of T3.

```lean
/-- T4: pure combination (no fuel, no bridge). The state-side facts are about `sp` and `st`; the `d`-side premises are about the same `sp`. -/
theorem shapeAgree_of_sides {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn) :
    ShapeAgree d st

/-- T5: fuel model → `ShapeAgree` for the run's own `sp`: the `d`-side premises of T4 are kept, `st` is produced by the run. -/
theorem shapeAgree_of_fuel_run {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn) :
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st

/-- T6: connection to production, **conditional on the boundary `ShapeFuelBridge` (inline hypothesis `hbr`, assumed once, not proved)**. -/
theorem shapeAgree_of_production {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    (h : machineShape? false [] E senv = some sp) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn) :
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st
```
`hbr` is written out in the type, not named, so no new `def` and no new shared Prop appears; the same text as `SRC_ARGW_SUPPLY_FREEZE.md` §2 (`allowInsts` of `machineShape?` is the default `true`, matching the trailing `true`).
T6 is **not a supply** of ShapeAgree for production: it holds only under `hbr`, and `hsp/hss/hls/hn` (row 6b) are unsupplied premises. The ordinary `hbr` is the single occurrence of the boundary in the new file.

Proof plan (to be confirmed by elaboration; not claimed): T1 by the same `unfold shapePost … repeat' first | ite_none_inv | bind_inv | …` pattern as `shapePost_insts'`, ending with `⟨rfl, by simp [machSlotFields_length]⟩`;
T2 from T1 + `shapePost_insts'`/`shapePost_instOrigins` + `hL.inits` (`min a a = a` after `inits.size = kinds.size`); T3 from `machineShapeF_steps` + `machineShapeF_lenOk` (the `st` of the two must be the same: obtain `LenOk` for the `st` of `machineShapeF_steps` by re-running the three in-tree phase lemmas `shapeStart_lenOk`, `rootLets_lenOk`, `shapeBody_lenOk`, not by two separate existentials);
T4 by `⟨hs.1 ▸ …⟩` after `subst hsp`; T5 = T3 + T4; T6 = `hbr` + T5.

## 3. Checks planned (`Tests/Gen5/Cover5Check.lean`, form of `Cover4Check.lean`; counts reported as real numbers with category and rule: one compared declaration = 1)

* **TYPE**: T1–T6 (6 declarations) against `Exp…` statements written from §2 independently of the Tools file (own spelling of the layout/`min`/`LenOk`/`hbr` text, not copied from the Tools file), by the same reducible comparer `checkExpected` with positive controls.
* **MUTANT** (signature/defeq rejection, **not** semantic counterexamples), each well-typed and rejected by the same comparer: T1 with `max` for `min`; T2 conclusion with one conjunct dropped (the `instOrigins` one); T2 without `hL`; T3 with `st.lets.size` replaced by `st1.lets.size` (single-variable change); T3 without the `shapePost … = some sp` clause (decouples `st` from `sp`); T4 without `hsp` (the identification premise); T4 without `hn`; T6 without `hbr`.
* **AXIOMS**: `collectAxioms` per theorem, standard only. **CLOSURE**: value-closure walk as in Cover4Check with its 3 negative / 2 clean controls and the unknown-name controls (unknown names `throwError`); intended `sorry` negatives built in memory inside `withoutModifyingEnv`, warning count N observed in the Pod and stated in the header. Source: no `sorry`, axiom, `native_decide`.
* Build: `kjob lake build Tools.ShippingGen5Cover5`, then `Tests.Gen5.Cover5Check`, one at a time, logs outside the tree; success SHA recorded by a comment-only commit. Two `lean_lib` additions to `lakefile.lean`. The Lean commit is left `doing` with "clean build は coder".

## 4. Not claimed

* Row 6a is proved (if it elaborates) **for the fuel model only**; for production only under the inline `ShapeFuelBridge` hypothesis. Not a supply for the real reader.
* Row 6b (`d.shape = sp`, `d.ss.length`, `d.ls.length`, `d.nIn`) is not implemented; T4–T6 take it as premises. `ShapeAgree` for any real run is not established.
* Remaining unsupplied rows keep their rev5 status: R-trace/R-in/R-nl/R-dom/B3 (row 1–5, 7, 8: 未供給 / この調査で経路未発見), `LetQuoteEq`, `LetsNoLoose`, `FullInv`, `d.ok = true` for a run, real reader connection, `ShapeFuelBridge`. Not completion of the Issue or FG.
* No new law, TRUSTED boundary, FG/guarantee change, compiler or shared-definition change; `GenWF` not strengthened.

## 5. Implementation addendum (g5cv-r11; non-blocking wording fix + status)

* §0 wording corrected: the production connection with `ShapeFuelBridge` is **T6** (not T5); T5 is the fuel-model step.
* Implemented as `Tools/ShippingGen5Cover5.lean` (T1–T6, statements as §2, no added premise, no new `def`/`structure`/`axiom`) and `Tests/Gen5/Cover5Check.lean`; two `lean_lib` entries in `lakefile.lean`.
* **Phase trace.** T3's witness (`p en st0 env st1 st v` with the six run equations and `shapePost … = some sp`, plus `st.LenOk` and the four facts of that `st`) together with T4 is the form later connections (R-trace etc.) must use.
  T5/T6 conclude only `∃ st, st.LenOk ∧ ShapeAgree d st`, which forgets the phase trace; that `st` must **not** be identified with any other existential witness of a run.
* Check counts (category and rule: one compared declaration = 1): TYPE 6 theorems; MUTANT 8 (T1 `max`, T2 drop `instOrigins` conjunct, T2 no `hL`, T3 `st1.lets.size`, T3 drop `shapePost` clause, T4 no `hsp`, T4 no `hn`, T6 no `hbr`; signature/defeq rejections, not semantic counterexamples);
  AXIOMS 6 theorems, standard only (T4 none); CLOSURE 5040 constants with 3 negative / 2 clean controls and 3 negative / 1 clean unknown-name controls; 3 intended `sorry` negatives (3 warnings); no `sorry` in either source.
* Closure check fix: the substring test for forbidden names now looks for `native_decide` (the earlier `native` substring matched `instAlternativeOption`); `Lean.ofReduceBool`/`trustCompiler`/`sorryAx` stay in the forbidden list.
* Still not supplied: row 6b (premises `hsp hss hls hn`), `ShapeFuelBridge` (inline `hbr`, assumed), R-trace/R-in/R-nl/R-dom/B3, `LetQuoteEq`, `LetsNoLoose`, `FullInv`, `d.ok`; production/Issue/FG are not complete.
