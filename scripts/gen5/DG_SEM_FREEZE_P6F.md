# DG-SEM freeze P6f — next unit U6D `srcCausal_of_acc_unfold / factsOf_of_acc_unfold / factsOf_all_of_acc_unfold` (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated in this commit.** Agent g5sm-u14, base `3b3ebe62` (= U6C approved at `343faecd`, build `smu13v-343faecd` exit 0, 716 jobs; `3b3ebe62` is a comment/docs sync only).
Everything is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit, no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree (read at `3b3ebe62`); `[br:X@sha]` = another branch (NOT in this tree; the SEM lineage is before S1 / DG-ACC / DG-DATAOF integration, so re-check at the integration SHA); `[N]` = new here.
Method: names and statement heads were read with `git show` / `grep` / `Read`; nothing was elaborated. "未供給 / この調査で経路未発見" = this survey found no route; it does not claim none exists. Audit = kernel types/values reachable from the roots, not opaque implementations or compiled code.

## 1. Sync (done, comment/docs only, no rebuild)
`Tools/ShippingGen5SemSrcCausal.lean` and `Tests/Gen5/SemSrcCausalCheck.lean` headers now state build `smu13v-343faecd` exit 0 (716 jobs), approved at `343faecd` (conditional on `hQ`); `DG_SEM_FREEZE_P6E.md` §2 row 5a says conditional-implemented. Commit `3b3ebe62`. The approval is for the conditional U6C unit only.

## 2. DG-SEM-owned rows after U6C, and what this survey found
| # | row | route found (real names) | owner | status |
|---|---|---|---|---|
| 1-3, 5a | `GenFacts`/`CombFacts`/`FactsOf (genSemI Q X g)`, `SrcCausal (genSemI Q X g)` | `genFacts`, `genSemI_srcCausal` `[B]` | DG-SEM | 条件付き実装済み（`hQ : CalleesCausal Q g.d` 条件） |
| 5b | `CalleesCausal (genS K) d` for the real table (P10 induction) | the step is `genSemI_srcCausal` `[B]`; the induction needs, per entry, "`G Y = some s` ⇒ `s = genSemI G Y g` and every ordinary callee is `R`-below `Y`". DG-ACC has the pieces on its branch: `genS_some_inv` (`s = K.genSem (genS K) X g`, `Acc (CallRel K) X`), `callEdge_of_ord`, `mem_ordCallees` `[br:g5ac-r14 Tools/ShippingGen5Acc.lean:72,143]`; DG-SEM has `mem_ordCallees`, `genSemVia` `[B Tools/ShippingGen5SemCall.lean:155,106]`. | DG-SEM (abstract form, **this unit U6D**) / DG-ACC (instantiation) | **first unit: U6D** (abstract in `G`, `R`; no `AssignKit`) |
| 4 | `GenSFacts K` (`∀ X s, genS K X = some s → FactsOf s`) `[br:g5ac-r14 Tools/ShippingGen5AccGenP.lean:23]` | `factsOf_all_of_acc_unfold` (U6D) gives exactly this shape for any `G`, `R` satisfying the unfolding premise `hunf`; supplying `hunf` for `G := genS K` needs `K.genSem = genSemVia K.GD toIn` (a kit-spec fact about `GenData.toIn`, DG-SEM/DG-DATAOF) | DG-ACC / DG-SEM | 未供給（`hunf` for the real `genS`, in particular `GenData.toIn` and the identification `K.genSem Q X g = genSemI Q X (toIn g)`、この調査で経路未発見） |
| 6 | `hp`, `hq` (U5E) | `[br:g5ac-r8 AccGenP]` | DG-ACC | 未供給 |
| 7 | `GenIn` supply (`dataOfAt_sound`, `GenWF` coverage, `GenData.toIn`) | `[br:g5do-r6]`, `[br:g5cv-r13]` | DG-DATAOF / DG-COVER / readertrace | 未供給 |
| 8 | `hord` | `T2-TIE` consumer | sparkle-gen5-t2-tie | consumer-supplied |
| 10 | `genS_some_inv_of_unfold` | DG-ACC already states `genS_some_inv` in kit form `[br:g5ac-r14 Acc.lean:143]`; a second abstract copy is **not** needed unless DG-ACC asks | DG-SEM → DG-ACC | not planned; this survey saw no consumer that the kit form fails to serve |
| — | `CalleesCausal` quantifies over all `s` with `Q c = some s`, and `genSemI_not_loop` `[B SemCall.lean]` is already available for the `.loop` exclusion | | | |

Other issues (DG-ACC, DG-DATAOF, DG-COVER, readertrace, T2-TIE): named only; no state changed, no row taken over.

**First unit and why: U6D = row 5b/4 in abstract form.** (1) It is the only remaining DG-SEM-owned row for which this survey found a complete route from existing names (U6C `genSemI_srcCausal`, `genFacts`, `mem_ordCallees`); (2) it removes the `hQ` premise of `genFacts` for any table that satisfies the unfolding shape, i.e. it is the "P10 step with an `Acc` induction" REV2 §7 splits between DG-SEM (step) and DG-ACC (instantiation); (3) it needs no `AssignKit`, `dataOf`, real run or `GenData` (none is in this tree); (4) row 4's remaining premise `hunf` for the real `genS` is the explicit residual, not hidden.
Ownership note: REV2 §7 gives "the `Acc` induction" to DG-ACC. U6D states the induction **abstractly** over an arbitrary relation `R` and table `G` (same device as REV2 §7's `genS_some_inv_of_unfold`), so DG-ACC can instantiate `G := genS K`, `R := CallRel K` without a second proof. If the reviewer prefers that DG-ACC own even the abstract form, U6D is the unit to hand over unchanged.

## 3. U6D — complete types
New file `Tools/ShippingGen5SemAccStep.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, imports `Tools.ShippingGen5SemSrcCausal` (it already imports `Tools.ShippingGen5SemFacts`); same `variable {ι : Type} {dom : ι → DomainConfig}` and `open`s as `Tools/ShippingGen5SemSrcCausal.lean`. No new `def`. Lakefile: one `lean_lib` for the file, one for its Check.

```lean
theorem srcCausal_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s) :
    SrcCausal s

theorem factsOf_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s) :
    FactsOf s

theorem factsOf_all_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (hacc : ∀ (Y : Name) (s : SemPkg ι dom), G Y = some s → Acc R Y) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s
```
Reading: `R c Y` = "`c` is an ordinary callee of `Y`" (DG-ACC's `CallRel K c Y = CallEdge K Y c`; `Acc R Y` quantifies over such `c`). `R` is an arbitrary relation: it may contain the ordinary-edge pairs and need not be equivalent to the callee relation (no iff with callees is required). `hunf` is a **premise** about the table, not a law; it is what `genS_some_inv` + `callEdge_of_ord` + `K.genSem = genSemVia …` would give for the real table, and **this unit does not supply it**. `ordCallees`, `genSemI`, `SrcCausal`, `FactsOf`, `GenIn` `[B]`.

Proof plan.
- `srcCausal_of_acc_unfold`: `Acc.induction` on `hX` (motive `∀ s, G X = some s → SrcCausal s`). Given `Y`, IH, `s` with `G Y = some s`: `hunf` gives `g`, `s = genSemI G Y g`, callee edges. `CalleesCausal G g.d` unfolds to `∀ k ∈ ordCallees g.d, ∀ s', G (insts[k]).1 = some s' → SrcCausal s'`; each is `IH _ (edge) s' hs'`. Then `genSemI_srcCausal G Y g hQ`.
- `factsOf_of_acc_unfold`: same induction is not needed again: `hunf` at `X` gives `g`; `hQ` from `srcCausal_of_acc_unfold` at each callee (which is `Acc`-below by `hX`'s inversion); `genFacts G X g hQ`, rewritten by `s = genSemI G X g`.
- `factsOf_all_of_acc_unfold`: `factsOf_of_acc_unfold` with `hacc X s hs`.

**Known delicate points (reported if they fail):** inverting `Acc R X` to `Acc R callee` (`Acc.inv`); `subst` of `s = genSemI …` direction; `Fin`-indexed `insts[k]` vs `ordCallees g.d` element type (`mem_ordCallees` is stated for `Fin`; the `∀ k ∈ ordCallees g.d` form is used as in `CalleesCausal`). If a statement must change on first elaboration, that is reported as a stop, not patched by adding a hypothesis silently.

### 3.1 Check (new file `Tests/Gen5/SemAccStepCheck.lean`, Expected written from the sentences above, not from the implementation)
Same requirements as `SemSrcCausalCheck`:
- **TYPE**: three theorems against independently written `Exp*` statements (`checkExpected`/`cmpTele`, reducible).
- **MUTANT** (well-typed single changes; rejection = signature/defeq, **not** a semantic counterexample; ill-typed proposals are not counted): drop `hunf`'s callee-edge conjunct (1); drop `hX` from `srcCausal_of_acc_unfold` (1); drop `hacc` from `factsOf_all_of_acc_unfold` (1); conclusion `SrcCausal` replaced by `CalleesCausal G g.d`-free wrong target e.g. `FactsOf s` in theorem 1 (1); `hunf` equation `s = genSemI G Y g` replaced by `s = genSemI (fun _ => none) Y g` (1); `R` argument order flipped in the edge conjunct `R Y callee` (1); theorem 2 stated with `SrcCausal` (wrong conclusion, 1). Adding an unused extra hypothesis makes the proposition weaker (not stronger) and is NOT counted. Real counts and the counting rule are printed by the Check.
- **AXIOMS**: standard only. **sorry**: absent.
- **CLOSURE**: explicit walk (unknown name ⇒ `throwError`) with controls: unknown root, forbidden roots (`sorryAx`, `Lean.ofReduceBool`) flagged by the root itself, unknown helper value (`Mv`), unknown helper type (`Mt`), clean fixture; fixtures only inside `withoutModifyingEnv`; positive and negative controls.
- **REACH**: `srcCausal_of_acc_unfold` reaches `genSemI_srcCausal`; `factsOf_of_acc_unfold` reaches `genFacts` and `srcCausal_of_acc_unfold`; `factsOf_all_of_acc_unfold` reaches `factsOf_of_acc_unfold`.

## 4. Not claimed
- `CalleesCausal` for the real `genS` table, `GenSFacts K`, `hp`/`hq`, `GenIn` supply, `GenData.toIn`, real runs, FG/M5/DG-ACC completion: **not supplied**. U6D only gives a conditional implication (`hunf` ⇒ facts for the pointwise forms; `hunf` + `hacc` ⇒ facts for the whole-table form); `hunf` for the real table 未供給 / この調査で経路未発見.
- Mutants are rejected by signature/defeq; they are not semantic counterexamples.
- SEM lineage is before S1; every claim is re-verified at the integration SHA. No new law/TRUSTED; if instantiating `hunf` turns out to need one, a decision document is written then (not now).

## 5. Wording corrections (reviewer notes at approval 204bbcb6, applied at implementation; no type changed)
- §3.1: an extra unused hypothesis makes the statement weaker, not stronger.
- §4 / `factsOf_all_of_acc_unfold`: conditional on `hunf` **and** `hacc`.
- `R c Y` is any relation containing the ordinary-edge pairs; equivalence with the callee relation is not required.
- Still unsupplied: `hunf`/`hacc` for the real `genS`, `GenData.toIn`/kit identification, real run/FG, integration re-verification.
