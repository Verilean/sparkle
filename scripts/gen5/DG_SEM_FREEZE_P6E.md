# DG-SEM freeze P6e — next unit U6C `extJoint_of_genSem / genSemGen_srcCausal / genSemComb_srcCausal / genSemI_srcCausal` (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated in this commit.** Agent g5sm-u12, base `a9a088d4` (= U6B approved at `7b5b844f`, build `smu11v-7b5b844f` exit 0, 714 jobs; `a9a088d4` is a comment/docs sync only).
Everything is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit, no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree (read at `a9a088d4`); `[br:X@sha]` = another branch (NOT in this tree; SEM lineage is before S1 / DG-ACC / DG-DATAOF integration, so re-check at the integration SHA); `[N]` = new here.
Method: names and statement heads were read with `git show` / `grep` / `Read`; nothing was elaborated. "未供給 / この調査で経路未発見" = this survey found no route; it does not claim none exists. Audit = kernel types/values reachable from the roots, not opaque implementations or compiled code.

## 1. Sync (done, comment/docs only, no rebuild)
`DG_SEM_FREEZE_P6D.md` §2 rows 1-3 now read "条件付き実装済み（hQ 条件、approved at 7b5b844f）"; `Tools/ShippingGen5SemFacts.lean` and `Tests/Gen5/SemFactsCheck.lean` headers state build `smu11v-7b5b844f` exit 0 (714 jobs). Commit `a9a088d4`.

## 2. Supplier table after U6B (rows owned by DG-SEM, then names of rows owned elsewhere)
| # | row | route found (real names) | owner | status |
|---|---|---|---|---|
| 1-3 | `GenFacts`/`CombFacts`/`FactsOf (genSemI Q X g)` | `genFacts_gen/comb`, `genFacts` `[B Tools/ShippingGen5SemFacts.lean]` | DG-SEM | 条件付き実装済み（`hQ : CalleesCausal Q g.d` はgen armのみ、approved at 7b5b844f） |
| 5a | step `SrcCausal (genSemI Q X g)` from `CalleesCausal Q g.d` (the "P11 step") | **route found in this survey**, see §3: the joint-causality form `src_causal_of_data_causal` `[B Tools/ShippingMachineCausalCtx.lean]` (takes `hjoint` over `Ctx`/`CtxAgree`, varies `bools`/`bits`/`S` together) + `callOut_causal` `[B SemCausal]` (already stated for differing `st st'`) + `typedVal_congrB` `[B ShippingMachineCausal.lean:30]`. The earlier P6d note ("`src_causal_of_data_ext` is pointwise, not the `extB`+`HCausalOf` form") is superseded: the unused `_ctx` variant is the matching one. | **DG-SEM** | **first unit: U6C** |
| 5b | `CalleesCausal Q g.d` for the real table (P10 `Acc` induction using 5a) | needs `Acc`/`genS` and the unfolding `genS K X = some s → s = genSemI …` | DG-ACC | 未供給 (named, not implemented here). Note for DG-ACC: `CalleesCausal` quantifies over any `s` with `Q c = some s`; U6C supplies the `.gen`/`.comb` arms only, so the table argument must show callees come from `genSemI` (never `.loop`; `LoopSem` is "never produced by genSem" `[B SemPkg.lean]`). |
| 4 | `GenSFacts K` | row 3 + 5b + `genS`↔`genSemI` unfolding | DG-ACC / DG-SEM | 未供給 |
| 6 | `hp`, `hq` (U5E) | `[br:g5ac-r8 AccGenP]` | DG-ACC | 未供給 |
| 7 | `GenIn` supply (`dataOfAt_sound`, `GenWF` coverage, `GenData.toIn`) | `[br:g5do-r6]`, `[br:g5cv-r13]` | DG-DATAOF / DG-COVER / readertrace | 未供給（`GenData.toIn` この調査で経路未発見） |
| 8 | `hord` | `T2-TIE` consumer | sparkle-gen5-t2-tie | consumer-supplied |
| 10 | `genS_some_inv_of_unfold` | text in `DG_SEM_FREEZE_REV2.md §7`, no Lean | DG-SEM | U6D candidate (needs `genS` from DG-ACC) |

**First unit and why: U6C = row 5a.** (1) It is the only remaining DG-SEM-owned row for which this survey found a complete route from existing lemmas; (2) 5b (P10) cannot start without it; (3) it needs no `dataOf`, `Acc`, or real run; (4) rows 4/6/7 are owned elsewhere or have no route found; row 10 depends on DG-ACC's `genS`.

## 3. U6C — complete types
New file `Tools/ShippingGen5SemSrcCausal.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, imports `Tools.ShippingGen5SemFacts` and `Tools.ShippingMachineCausalCtx`; same `variable {ι : Type} {dom : ι → DomainConfig}` and `open`s as `Tools/ShippingGen5SemCausal.lean` (plus `open Tools.ShippingMachineCausal (Ctx CtxAgree)`). No new `def`. Lakefile: one `lean_lib` for the file, one for the Check.

```lean
theorem extJoint_of_genSem (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    ∀ (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
      (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val t) ∧
      (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t)

theorem genSemGen_srcCausal (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    SrcCausal (SemPkg.gen (genSemGen Q X g))

theorem genSemComb_srcCausal (X : Name) (g : GenIn) :
    SrcCausal (SemPkg.comb (genSemComb (ι := ι) (dom := dom) X g))

theorem genSemI_srcCausal (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    SrcCausal (genSemI Q X g)
```
(`SrcCausal`, `CalleesCausal`, `extOf`, `extBOf`, `genSemGen`, `genSemComb`, `genSemI` `[B]` at `a9a088d4`; `Ctx`/`CtxAgree` `[B Tools/ShippingMachineCausalCtx.lean]`, namespace `Tools.ShippingMachineCausal`. If a prefix differs on first elaboration that is a name fix, reported, not a statement change.)

Helper lemmas `[N]`, outside Expected (listed in the Check message): `ExtStage_causal2` — the `ExtStage_causal` induction with the input families also varying: hypotheses `hS : ∀ c ≤ t, S.val c = S'.val c`, `hB : ∀ c ≤ t, (∀ p, (bools p).val c = (bools' p).val c) ∧ ∀ p w, (bits p w).val c = (bits' p w).val c`, conclusion both components of `ExtStage Q g i bools bits S n` / `ExtStage Q g i bools' bits' S' n` agree at `t`; and `map_apply_eq_of_getElem` : `l.length = l'.length → (∀ k f f', l[k]? = some f → l'[k]? = some f' → f t = f' t) → l.map (· t) = l'.map (· t)`.

Proof plan.
- `ExtStage_causal2`: induction on `n` generalizing `t`; step = `callOut_causal Q g hQ i S S' n t _ _ hS (fun c hc => ih c (…≤c from ≤t…) (…))` — `callOut_causal` already takes `st st'` (stated that way in U6A), so no new case analysis.
- `extJoint_of_genSem`: `ExtStage_causal2` at `n = g.d.shape.insts.length` with `hS := h.2.2`, `hB := fun c hc => ⟨fun p => h.1 p c hc, fun p w => h.2.1 p w c hc⟩`; result order `⟨.2, .1⟩` as in `extCausal_of_genSem`.
- `genSemGen_srcCausal`: obtain `genFacts_gen Q X g hQ (genSemGen Q X g) rfl`-shaped `GenFacts`; apply `Tools.ShippingMachineCausal.src_causal_of_data_causal` (arguments = the fields `ok body_eq init writes result source`, `causal` for `_hcausal`, `extJoint_of_genSem` for `hjoint`) to get the element-wise statement `∀ k f f', … → f t = f' t`; list-length equality from `result` (both sides `d.outs.map …`, so length `g.d.outs.length`); close by `map_apply_eq_of_getElem`.
- `genSemComb_srcCausal`: unfold; `List.map_congr`-style with `typedVal_congrB` at `t` (the state `g.inits` is fixed); no `hQ`.
- `genSemI_srcCausal`: `unfold genSemI; split`, arms by the two theorems above.

**Known delicate points (reported if they fail):** instance argument `[Inhabited (HList (tys d.ss))]` of `src_causal_of_data_causal` after `subst` (`⟨g.inits⟩` vs `s.inh`; U6B needed an explicit `@`); implicit `declName`; `SrcCausal`'s `Signal.val` hypotheses are `∀ c ≤ t, (∀ j, (A j).val c = …) ∧ ∀ j n, …` — different packaging than `hb`/`hv` of the lemma, one adapter step. If the length-equality step cannot be closed from `result` alone, that is reported as a stop, not patched by weakening `SrcCausal` or the statement.

### 3.1 Check (new file `Tests/Gen5/SemSrcCausalCheck.lean`, Expected written from the sentences above, not from the implementation)
Same requirements as `SemFactsCheck`:
- **TYPE**: four theorems against independently written `Exp*` statements with the reducible comparer `checkExpected`/`cmpTele`; `Exp*` reproduces `Ctx`/`CtxAgree` unfolded where possible, or by the same names `[B]`.
- **MUTANT** (well-typed single changes; rejection = signature/defeq, **not** a semantic counterexample; ill-typed proposals are not counted): drop `hQ` from `extJoint_of_genSem`, from `genSemGen_srcCausal`, from `genSemI_srcCausal` (3); `extJoint` conclusion at `t+1` on the right (1); `extJoint` hypothesis `CtxAgree x x' t` replaced by `CtxAgree x x' (t+1)` (1); `genSemI_srcCausal` stated for `SemPkg.gen (genSemGen Q X g)` (wrong package, 1); `genSemGen_srcCausal` for `SemPkg.comb (genSemComb X g)` (wrong arm, 1); `genSemComb_srcCausal` with an extra unused hypothesis dropped-from-Expected direction — i.e. adding `(hQ : CalleesCausal Q g.d)` is NOT a mutant (stronger statement) and is not counted (0); `hQ : CalleesCausal Q g.d` replaced by `hQ : CalleesCausal Q (genSemI Q X g).d`-style change of `d` in `genSemGen_srcCausal` (1, if well-typed at elaboration; otherwise omitted and the count reflects it). Real counts and the counting rule are printed.
- **AXIOMS**: standard only. **sorry**: absent.
- **CLOSURE**: explicit walk (unknown name ⇒ `throwError`) with controls: unknown root, forbidden roots (`sorryAx`, `Lean.ofReduceBool`) flagged by the root itself, unknown helper value (`Mv`), unknown helper type (`Mt`), clean fixture; fixtures only inside `withoutModifyingEnv`; positive and negative controls for the closure and the root's own judgement.
- **REACH**: `genSemI_srcCausal` reaches `genSemGen_srcCausal`, `genSemComb_srcCausal`; `genSemGen_srcCausal` reaches `src_causal_of_data_causal`, `extJoint_of_genSem`, `genFacts_gen`; `extJoint_of_genSem` reaches `callOut_causal`.
- Builds: `kjob lake build Tools.ShippingGen5SemSrcCausal`, then `Tests.Gen5.SemSrcCausalCheck`, one at a time, on the tree to be committed; the clean issue-linked build is the coder's; the built SHA goes into the headers by a comment-only commit.

## 4. Not claimed
- U6C is **not** `CalleesCausal` for a real table (5b/P10: needs DG-ACC's `Acc`/`genS`), `GenSFacts` (row 4), `hp`/`hq`, `GenIn` supply (row 7), `GenWF` coverage, `genS_some_inv`, `CallOutRange`, M5 or FG. No real run is supplied.
- `genSemI_srcCausal` is conditional on `hQ : CalleesCausal Q g.d`; `g.wf` is a field of `GenIn` and this proof is not claimed wf-free. It covers the `.gen`/`.comb` arms of `genSemI` only; no `.loop` arm statement.
- No new law/TRUSTED is needed: all ingredients are existing lemmas `[B]`; no decision document required.
- SEM lineage is before S1; statements must be re-verified at the integration SHA.
