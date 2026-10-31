# DG-SEM freeze P7 — next unit U7 `hunf_of_kitInv` / `factsOf_all_of_kitInv` (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated in this commit.** Agent g5sm-u16, base `914090c8` (= U6D approved at `f7d72d28`, build `smu15v-f7d72d28` exit 0, 717 jobs; `914090c8` is a comment/docs sync only).
Everything is a PROPOSAL until approved. No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit, no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.
Marks: `[B]` = in this tree (read at `914090c8`); `[br:X@sha]` = another branch (NOT in this tree); `[N]` = new here.
Method: names and statement heads were read with `git show` / `grep` / `Read`; nothing was elaborated. "この調査で経路が見つからなかった" does not claim impossible. Audit = kernel types/values reachable from the roots, not opaque implementations or compiled code.

## 1. Sync (done, comment/docs only, no rebuild)
Headers of `Tools/ShippingGen5SemAccStep.lean` and `Tests/Gen5/SemAccStepCheck.lean` now state build `smu15v-f7d72d28` (exit 0, 717 jobs), approved at `f7d72d28`. `DG_SEM_FREEZE_P6F.md` §3.1: the edge-drop mutant was planned as 1, implemented as 2 variants (the Check prints the real count). Commit `914090c8`.

## 2. Survey: which of the remaining rows close from existing names (real names)
Remaining rows after U6D: (a) `hunf` for the real `genS`, (b) `hacc` for the real `genS`, (c) `GenData.toIn` / `K.genSem = genSemVia K.GD toIn` identification.

| row | route found (real names) | status |
|---|---|---|
| (b) `hacc` for `G := genS K`, `R := CallRel K` | 5th component of `genS_some_inv K : genS K X = some s → ∃ E g, entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧ (∀ k ∈ K.ordCallees (K.dOf g), ∃ sc, …) ∧ s = K.genSem (genS K) X g` `[br:g5ac-r18@7076f718 Tools/ShippingGen5Acc.lean:143]` | DG-ACC owns `genS_some_inv`; closes from it with no new premise once the kit is in the tree |
| (a) `hunf`, edge part | `callEdge_of_ord K hE hg : ∀ k ∈ K.ordCallees (K.dOf g), CallEdge K X ((K.dOf g).shape.insts[k]).1` `[br:g5ac-r18 Acc.lean:70]`; `CallRel K c X := flip (CallEdge K) c X` is defeq to `CallEdge K X c` (`abbrev`, `Acc.lean:76`) | DG-ACC lemma; closes the edge conjunct given the kit |
| (a) `hunf`, equation part `s = genSemI G Y g` | `genS_some_inv` gives `s = K.genSem (genS K) X g'` (`g' : K.GD E`). `genSemI G Y g` for a `GenIn g` needs `g = toIn g'` and `K.genSem Q X g' = genSemVia K.GD toIn Q X g'` (= `genSemI Q X (toIn g')`, `genSemVia` `[B Tools/ShippingGen5SemCall.lean:106]`, definitional). | **未供給**: `GenData` / `toIn` are NOT built in any tree this survey saw (`Tools/ShippingGen5T2Tie.lean` header: `ClosingRun, genSem, genP, GenData` of `DGEN_FREEZE.md` rev2 NOT BUILT). The identification is a statement about an object that does not exist yet; この調査で辿った候補経路では未供給 |
| (a) kit field `mem_ordCallees` vs ours | kit field `K.mem_ordCallees : k ∈ K.ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none` `[br:g5ac-r18 Acc.lean:45]`; ours `mem_ordCallees : k ∈ ordCallees d ↔ (originOf d k).child? = none` `[B SemCall.lean:~155]`, `originOf d k := d.shape.instOrigins.getD k .ord` `[B SemGen.lean:24]` | both sides are the same predicate; membership-equivalent without any new fact |
| (c) `toIn` itself, `dOf (g) = (toIn g).d` | DG-DATAOF `[br:g5do-r6]` owns `dataOf`/`GenData` side; DG-COVER `[br:g5cv-r13]` owns coverage | 未供給（名前を挙げるのみ、この Issue は取らない） |

Other Issues (DG-ACC, DG-DATAOF, DG-COVER, readertrace, T2-TIE): named only; no state changed.

**Finding.** `kjob/g5ac-r18` (DG-ACC) is not an ancestor of this branch; `Tools.ShippingGen5Acc` (`AssignKit`, `genS`, `genS_some_inv`, `callEdge_of_ord`) cannot be imported here without merging another Issue's lineage (not done; merge is out of scope). So the real-`genS` instantiation itself is an integration step (after DG-ACC/DG-DATAOF land). What *is* closable inside this lineage with real names is the **bridge from the kit-shaped data to the `hunf`/`hacc` shape of U6D**, with the kit's fields as explicit variables (they are exactly the `AssignKit` field types, so integration instantiates them verbatim) — this is U7.

## 3. First unit and why: U7 = kit-shaped bridge to `hunf` / whole-table facts
Reasons: (1) it is the only row for which this survey found a complete route from names present in this tree (`genSemVia`, `genSemI`, `ordCallees`, `mem_ordCallees`, `factsOf_all_of_acc_unfold`) plus kit-field types copied from `AssignKit`; (2) it does the part of (a) that is non-trivial in Lean and would otherwise be redone at integration: transport of the `Fin (d.shape.insts.length)` index across `(toIn gd).d = dOf gd` and the `ordCallees` / `K.ordCallees` membership match; (3) it needs no `AssignKit`, no `GenData`, no run, and adds no law (the kit identifications are **premises** `hsem`, `hd`, `hmem`, `hinv`); (4) the residual stays explicit: `hsem`, `hd` (the `toIn` identification) and `hinv` for the real `genS` are not supplied. Honest scope: `hacc` is not a separate theorem; it is the `Acc R X` component of the premise `hinv`, which at integration is the 5th component of `genS_some_inv`.

### 3.1 Complete types
New file `Tools/ShippingGen5SemKitInv.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, imports `Tools.ShippingGen5SemAccStep`, same `variable {ι : Type} {dom : ι → DomainConfig}` and `open`s as `Tools/ShippingGen5SemAccStep.lean` (`Lean` open so `ConstantInfo`, `Name` resolve). No new `def`. Lakefile: one `lean_lib` for the file, one for its Check.

```lean
theorem hunf_of_kitInv
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd) :
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y

theorem factsOf_all_of_kitInv
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s
```
`SemPkg`, `GenIn`, `genSemI`, `genSemVia`, `ordCallees`, `FactsOf`, `MachineData` `[B]`; `factsOf_all_of_acc_unfold` `[B Tools/ShippingGen5SemAccStep.lean]`.

Proof plan.
- Helper lemma `[N]` (inside the file, stated before use; reported if it needs a different shape): `∀ (d d' : MachineData), d = d' → ∀ k : Fin d.shape.insts.length, k ∈ ordCallees d → ∃ k' : Fin d'.shape.insts.length, k' ∈ ordC d' ∧ (d.shape.insts[k]).1 = (d'.shape.insts[k']).1` — `subst`, `k' := k.cast` is `k` after `subst`; membership by `mem_ordCallees` (`[B]`) + `hmem` (both unfold to the same `getD … child? = none`).
- `hunf_of_kitInv`: `intro Y s _ hs`; `obtain ⟨E, gd, hacc, hedge, hseq⟩ := hinv Y s hs`; witness `toIn gd`; equation `hseq.trans (hsem G Y gd)` (`genSemVia … = genSemI G Y (toIn gd)` by `rfl`/`unfold`); edge conjunct: helper with `hd gd` then `hedge`.
- `factsOf_all_of_kitInv`: `factsOf_all_of_acc_unfold R G (hunf_of_kitInv … ) (fun Y s hs => (hinv Y s hs).choose_spec.choose_spec.1)`.
- `Acc R Y` argument of `hunf` is unused in `hunf_of_kitInv` (the stated shape is weaker than needed; that is the shape U6D consumes).

**Known delicate points (reported if they fail):** `subst` direction of `d = d'` when `d' = dOf gd` is not a variable (resolved by the helper, quantified over `d d'`); `Fin` casts in `insts[k]`; if a statement must change on first elaboration it is reported as a stop, not patched by adding a hypothesis silently.

### 3.2 Check (new file `Tests/Gen5/SemKitInvCheck.lean`, Expected written from the sentences above, not from the implementation)
Same requirements as `SemAccStepCheck`:
- **TYPE**: two theorems against independently written `Exp*` statements (`checkExpected`/`cmpTele`, reducible).
- **MUTANT** (well-typed single changes only; rejection = signature/defeq, **not** a semantic counterexample; ill-typed proposals are not counted; the Check prints the real count): `hsem` target `genSemVia GD toIn Q X gd` → `genSemI (fun _ => none) X (toIn gd)`; drop `hd`; `hmem` `= none` → `≠ none`; `hinv` edge `R c X` → `R X c`; `hinv` equation `genSemK G X gd` → `genSemK (fun _ => none) X gd`; `hunf` conclusion edge `R c Y` → `R Y c`; `factsOf_all_of_kitInv` conclusion `FactsOf s` → `SrcCausal s`; drop the `Acc R X` conjunct of `hinv` in `factsOf_all_of_kitInv` (well-typed? the proof would not follow, but as a signature mutant it is a changed type; counted only if it type-checks as a statement). Adding an unused extra hypothesis makes the statement weaker and is NOT counted.
- **AXIOMS**: standard only. **sorry**: absent.
- **CLOSURE**: explicit walk (unknown name ⇒ `throwError`) with controls: unknown root, forbidden roots (`sorryAx`, `Lean.ofReduceBool`) flagged by the root itself, unknown helper value (`Mv`), unknown helper type (`Mt`), clean fixture; fixtures inside `withoutModifyingEnv`; positive and negative controls.
- **REACH**: `hunf_of_kitInv` reaches `genSemVia`/`genSemI` and `mem_ordCallees`; `factsOf_all_of_kitInv` reaches `factsOf_all_of_acc_unfold` and `hunf_of_kitInv`.

## 4. Not claimed
- `hsem`, `hd` (the `GenData.toIn` / kit identification), `hinv` for the real `genS K`: **not supplied**. At integration `hinv` is intended to be assembled from `genS_some_inv` + `callEdge_of_ord` (names above, read not elaborated) and `hmem := K.mem_ordCallees`; whether that assembly goes through is not verified here. `GenData`/`toIn` are not built; この調査で辿った候補経路では未供給.
- `CalleesCausal` for the real table is not claimed; U7 only gives a conditional implication on top of U6D.
- Real run, M5, FG, DG-ACC/DG-DATAOF/DG-COVER/readertrace rows, `GenSFacts K` for a built kit: not supplied. SEM lineage is before S1; every claim is re-verified at the integration SHA.
- No new law / TRUSTED. If supplying `hsem`/`hd` for a real `GenData` needs one, a decision document is written then (not now).
- Mutants are rejected by signature/defeq; they are not semantic counterexamples.
