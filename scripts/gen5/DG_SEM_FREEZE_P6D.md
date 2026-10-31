# DG-SEM freeze P6d — next unit U6B `genFacts_gen / genFacts_comb / genFacts` (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated in this commit.** Agent g5sm-u10, base `a3f99320` (= U6A approved at `c0d18b96` + comment-only header sync; build `smu9v-c0d18b96` exit 0, 712 jobs).
Everything is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit, no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree (read at `a3f99320`); `[br:X@sha]` = read in another branch (NOT in this tree; SEM lineage is before S1/DG-ACC/DG-DATAOF integration, so re-check at the integration SHA); `[N]` = new here.
Method: names/statement heads were read by `git show`/`grep`/`Read`; nothing was elaborated. "未供給 / この調査で経路未発見" = this survey found no route, not that none exists.

## 1. Header sync (done, comment-only, no rebuild)
`Tools/ShippingGen5SemCausal.lean` and `Tests/Gen5/SemCausalCheck.lean` headers now state: clean issue-linked build `smu9v-c0d18b96` exit 0 (712 jobs), approved at `c0d18b96` (the "not yet run" wording is removed). The sentence about `g.wf` is restricted to: *this proof does not invoke `g.wf`*; a `GenIn` still contains `wf`, so this is **not** a wf-free claim. Commit `a3f99320`.

## 2. Supplier table (rows after U6A)
`P : Pkgs ι dom`, `K : AssignKit` (DG-ACC). A row owned by another Issue is named, not re-implemented here.

| # | row (condition / fact) | route found (real names) | owner | status after this survey |
|---|---|---|---|---|
| 1 | `GenFacts` of the `.gen` arm of `genSemI Q X g` (fields `ok body_eq init writes result source causal`) | `GenIn.ok/bodyEq/init` `[B SemGen.lean:61]`; `genSemGenE_writes/result/source` `[B SemGen.lean:115,129,144]` (stated for any `eb ev`); `extCausal_of_genSem` `[B SemCausal]` (needs `CalleesCausal Q g.d`) | **DG-SEM** | **実装予定 (U6B; 通ったら closed に戻す)**, conditional on `hQ : CalleesCausal Q g.d` for `causal` only |
| 2 | `CombFacts` of the `.comb` arm (`ok hbody hinit hnext hres`) | `g.ok/bodyEq/init`; `hres` is the definition of `genSemComb.src` (`rfl`-shaped); `hnext` is `inits = evalTerms …` in `HList (tys g.d.ss)` with `g.d.ss = []` (from the `.comb` condition `g.d.ss.isEmpty`) — equality of two elements of `HList (tys [])` | **DG-SEM** | **実装予定 (U6B; 通ったら closed に戻す)** (no `hQ`) |
| 3 | `FactsOf (genSemI Q X g)` | by the `if` of `genSemI` `[B SemCall.lean:103]`: row 2 / row 1 | **DG-SEM** | **実装予定 (U6B; 通ったら closed に戻す)**, conditional on `hQ` |
| 4 | `GenSFacts K := ∀ X s, genS K X = some s → FactsOf s` `[br:g5ac-r8]` | row 3 at `s = genSemI (semOf P) X g` with `hQ` from row 5 | DG-ACC states `GenSFacts`; DG-SEM supplies row 3 | **未供給**: needs (a) row 5 and (b) the `genS`↔`genSemI` unfolding `genS_unfold` (DG-ACC) and `GenData.toIn` (row 7); U6B supplies only row 3 |
| 5 | `CalleesCausal Q g.d` for the real table: `genSemI_srcCausal` (P11 step) and `genS_srcCausal_acc` (P10) | P10: `Acc` induction, **DG-ACC** supplies `Acc`/`genS`, DG-SEM supplies the step. Step `SrcCausal (genSemI Q X g)`: located `src_causal_of_data` / `src_causal_of_data_ext` `[B Tools/ShippingMachineCausal.lean:407,495]` — their `ext` is *pointwise* in `(bools,bits,S(t))` with `bools` passed unchanged, **not** the `extB` + `HCausalOf` form of `GenFacts`. | DG-SEM (step) / DG-ACC (`Acc`) | **この調査で経路未発見** for the `extB`/`HCausalOf` form; a `stateLoop`-causality lemma over `HCausalOf` would be needed. Not in U6B. |
| 6 | `hp`, `hq` of U5E (`genP_generated`, `genP_pkg`) | `[br:g5ac-r8 AccGenP]`, `hF` = row 4 | DG-ACC (`genP`, kit A5/A6) | 条件付き, unchanged from P6c §2 rows 1-2; no new route found |
| 7 | `GenIn` from `dataOfAt_sound` + `GenWF` coverage; `GenData.toIn` | `dataOfFrom_sound/dataOfAt_sound` `[br:g5do-r6@063056d6]`; `genWF_iff` `[br:g5cv-r13]`; DG-COVER's U-D3 / `rowC_of_reader_ok` | DG-DATAOF / DG-COVER (reader-trace residue: `sparkle-gen5-dg-readertrace`) | unchanged: **未供給**; `GenData.toIn` **この調査で経路未発見** |
| 8 | `hord` | consumer's call selection (T2-TIE `callTie_of_served_oneOut_closing`) | `sparkle-gen5-t2-tie` | consumer-supplied; not all calls are ordinary |
| 9 | `genSemI_local`, `ExtStage_local` | `[B SemCall.lean:182,160]` | DG-SEM (done, U4B) | closed earlier |
| 10 | `genS_some_inv_of_unfold` (abstract in `G` and `hunf`, REV2 §7) | text in `DG_SEM_FREEZE_REV2.md §7`; **no Lean in this tree** | DG-SEM | not designed with a full telescope here; candidate for U6C |

**First unit and why:** U6B = rows 1-3. (1) owned only by this Issue; (2) every ingredient is built and approved: `genSemGenE_*` (U3), `extCausal_of_genSem` (U6A), `GenIn` fields; (3) it is the exact obligation `FactsOf` that `genPkg`, `toSem_genPkg`, `GenSFacts` (row 4) and `Pkg.trace` consume — row 4 cannot even be stated for DG-SEM's side without it; (4) it needs no `dataOf`, no `Acc`, no real run; (5) rows 4-7 are either owned elsewhere or have no located route, so they are not first.

## 3. U6B — complete types
New file `Tools/ShippingGen5SemFacts.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, imports `Tools.ShippingGen5SemCausal` (hence `SemCall`, `SemGen`, `SemPkg`) and `Tools.ShippingQuadComposed` (`GenFacts`) and `Tools.ShippingGen2CombPkg` (`CombFacts`) if not already transitively present; same `variable {ι : Type} {dom : ι → DomainConfig}` and `open`s as `Tools/ShippingGen5SemCausal.lean`. No new `def`. Lakefile: one `lean_lib` for the file, one for the Check.

```lean
theorem genFacts_gen (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d)
    (s : SrcSem ι dom) (hs : genSemI Q X g = SemPkg.gen s) :
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src

theorem genFacts_comb (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : CombSem ι dom) (hs : genSemI Q X g = SemPkg.comb s) :
    Tools.ShippingGen2.CombFacts s.d dom s.inits s.src

theorem genFacts (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    FactsOf (genSemI Q X g)
```
(`FactsOf` unfolds per arm to exactly the first two conclusions `[B SemPkg.lean:154]`. The exact namespace of `GenFacts` is read as `Tools.ShippingQuadComposed.GenFacts` from `Tools/ShippingQuadComposed.lean:106`; if the first elaboration shows a different prefix, that is a name fix, reported, not a statement change.)

Proof plan. `genFacts_gen`: `unfold genSemI at hs`; the `.comb` branch gives `SemPkg.comb _ = SemPkg.gen s` (constructor clash, `cases`); the `.gen` branch gives `s = genSemGen Q X g` (`SemPkg.gen.inj`), `subst`; fields `ok := g.ok`, `body_eq := g.bodyEq`, `init := g.init` (all by projection reduction of `genSemGen = genSemGenE …`), `writes := genSemGenE_writes X g (extBOf Q g) (extOf Q g)`, `result := genSemGenE_result …`, `source := genSemGenE_source …`, `causal := extCausal_of_genSem Q g hQ`. `genFacts_comb`: the `.gen` branch is a constructor clash; the `.comb` branch gives `s = genSemComb X g`; `ok/hbody/hinit` from `g`; `hres` by `rfl`-shaped unfolding of `genSemComb.src`; `hnext`: from the branch condition `g.d.ss.isEmpty = true` get `g.d.ss = []`, then the helper `∀ ss, ss = [] → ∀ x y : HList (tys ss), x = y` (by generalizing `ss`; `[N]` helper, not part of Expected). `genFacts`: `unfold genSemI; split`, `FactsOf` by `genFacts_comb` / `genFacts_gen` with `rfl`.
**Known delicate points (reported if they fail):** the instance argument `s.inh` of `GenFacts` after `subst`; `HList (tys [])` equality needing `ss` as a variable; `FactsOf` unfolding through the `if` with `Bool` condition `&&`. If `hnext` cannot be closed without extra structure of `HList`, that is reported as a stop, not patched by weakening the statement.

### 3.1 Check (new file `Tests/Gen5/SemFactsCheck.lean`, Expected written from the sentences above, not from the implementation)
- **TYPE**: three theorems against independently written `Exp*` statements (the `GenFacts`/`CombFacts` instances written with explicit `@`-telescope, not via `FactsOf`; `genFacts` against `∀ …, FactsOf (genSemI Q X g)` written from the `if`-free sentence) with the same reducible comparer `checkExpected`/`cmpTele` as `SemCausalCheck`.
- **MUTANT** (well-typed single changes; rejection is by signature/defeq, **not** a semantic counterexample): drop `hQ` from `genFacts_gen`; drop `hQ` from `genFacts`; `hs` for `.comb` instead of `.gen` in `genFacts_gen`; conclusion `CombFacts` replaced by `GenFacts`-shaped for the other arm; `genFacts` for `genSemGen` instead of `genSemI` (wrong package); `s.inits` replaced by `g.inits` in `genFacts_comb` (not defeq as a statement because `s` is free). Counted as: mutants on theorems N, with the per-mutant rule listed in the Check message.
- **AXIOMS**: standard only. **sorry**: absent.
- **CLOSURE**: the explicit walk of `SemCausalCheck` (unknown name ⇒ `throwError`); controls: unknown root, forbidden roots (`sorryAx`, `Lean.ofReduceBool`) flagged by the root itself, unknown helper value (names `Mv`), unknown helper type (names `Mt`, path through the existing helper), clean fixture; fixtures only inside `withoutModifyingEnv`; intended names asserted.
- **REACH**: `genFacts` reaches `genFacts_gen`, `genFacts_comb`; `genFacts_gen` reaches `genSemGenE_writes`, `genSemGenE_result`, `genSemGenE_source`, `extCausal_of_genSem`.
- Numbers are reported as real counts per category with the counting rule beside them. Builds: `kjob lake build Tools.ShippingGen5SemFacts`, then `Tests.Gen5.SemFactsCheck`, one at a time, **on the tree that will be committed** before committing; the clean issue-linked build is the coder's; the built SHA goes into the headers by a comment-only commit.

## 4. Not claimed
- U6B is **not** `hp`, `hq`, `GenIn`, `GenWF` coverage, `Acc`, `GenSFacts` (row 4), `CalleesCausal` for a real table (row 5: no route found for `genSemI_srcCausal`), P10, `genS_some_inv`, `CallOutRange`, M5 or FG. No real run is supplied.
- `genFacts` is conditional on `hQ : CalleesCausal Q g.d`; `g.wf` is a field of `GenIn` and U6A's proof does not invoke it, which is not a wf-free claim.
- The SEM lineage is before S1 (only the T2Tie pattern fix is integrated); statements must be re-verified at the integration SHA.

## 5. Addendum (U6B implementation, agent g5sm-u11) — corrections to §3.1 mutants
Reviewer finding at approval: `s` is a free `CombSem`/`SrcSem`, so putting `g.inits : HList (tys g.d.ss)` where `s.inits : HList (tys s.d.ss)` is expected is ill-typed, and substituting the other constructor for `s` in `hs` is ill-typed too. **These are not counted as rejected mutants.** The implemented Check uses only well-typed single changes (rejection by signature/defeq, not a semantic counterexample):
1. `genFacts_gen` without `hQ`; 2. `genFacts` without `hQ`; 3. `genFacts_gen` without `hs`; 4. `genFacts_comb` without `hs`;
5. `genFacts_gen` with `hs : genSemGen Q X g = s` (instead of `genSemI … = .gen s`); 6. `genFacts_gen` with `hQ : CalleesCausal Q s.d` (on `s.d` instead of `g.d`);
7. `genFacts_gen` conclusion `src` replaced by `(genSemGen Q X g).src` (same type); 8. `genFacts_comb` conclusion `src` replaced by `(genSemComb X g).src`;
9. `genFacts` stated for `FactsOf (SemPkg.gen (genSemGen Q X g))` (wrong package).
Count rule: one mutant = one well-typed statement differing from the Expected by one edit. Conclusion-conjunct-dropped mutants: 0 (the conclusions are `GenFacts`/`CombFacts` structures, not conjunctions).
Implementation note: one extra helper `hlist_nil_subsingleton` (outside the frozen statements). `GenFacts.mk` is applied with `@` and the instance `(genSemGen Q X g).inh` given explicitly (anonymous-constructor instance synthesis failed after `subst`); no statement changed, no extra hypothesis.
