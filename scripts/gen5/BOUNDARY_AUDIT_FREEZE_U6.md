# BOUNDARY-AUDIT freeze U6 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit`. Branch `kjob/g5ba-r12`, base `7bb90c04` (= U5 approved `76ae2e8e` + comment-only header sync to build `ba11v-76ae2e8e`, exit 0, 724 jobs). This file ADDS to `BOUNDARY_AUDIT_FREEZE*.md` (U1-U5); nothing there is withdrawn.
"Not found" means only that this survey did not find a supplier or a route; it does not say a row is impossible or underivable. Nothing here claims N1, G5, G7, M5, FG or Issue completion.
No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing or GenWF strengthening is proposed. No decision document is needed.

## 0. U5 sync (done, comment only, commit 7bb90c04)
Headers of `Tools/ShippingGen5NameKids5.lean` and `Tests/Gen5/NameKids5Check.lean` record the reviewed build ba11v-76ae2e8e (MUTANT 4 are single-point; rejection is by signature/defeq, not a semantic counterexample).
Maintained: `hfo` is a sufficient condition (reached `c` has `FirstOcc ds c d` and `S c = some d.shape`), not equivalent to `GraphAgrees`; its supply from the production `ds` / `Reach` / `S`, InClass, ReachSpans, production bridge, N1 / G5 / G7 / M5 / FG are unsupplied.

## 1. Survey of the remaining rows (existing names, full types)

| row | existing lemma in THIS tree | closes? |
|---|---|---|
| `hfo` (production `ds` ↔ `Reach` / `S`) | `Tools.ShippingSrm15Graph.GraphCovers (ds : List (Name × MachineData)) : Prop := ∀ p ∈ ds, ∀ k ∈ p.2.shape.instTagged, k.2.child? = none → ∃ d' : MachineData, FirstOcc ds k.1 d'` and `DefsProv` are STATED provenance Props (premises); the link of `ds` to `T1Hyp`'s `P` / `Reach` was not found in this survey | 未供給 / この調査で経路未発見 |
| `InClass g B top = true` (`InClass g B top := WfG g && (declRank g B top).isSome`; `WfG g := (g.map Prod.fst).eraseDups.length == g.length`) | `Srm7Rank.inClass_rank` is the CONSEQUENCE direction only. For `g := graphOf ds` (`graphOf ds := ds.map fun p => (p.1, p.2.shape.instTagged)`) the `WfG` conjunct depends only on the names of `ds` (`(graphOf ds).map Prod.fst = ds.map Prod.fst`, by `List.map_map`); no lemma stating this was found in the tree | **Yes, the `WfG` half** closes from existing names as a conditional theorem (§2). The rank half `(declRank (graphOf ds) B top).isSome` for the generated program: 未供給 / この調査で経路未発見 |
| `ReachSpans g top Reach` (`∀ c, Reach c → OrdPath g top c`) | none (converse of `ReachClosed`; `ReachClosed` alone does not give minimality) | 未供給 / この調査で経路未発見 |
| production link `machineShape?` ↔ `machineShapeF`; (c) ordinary child name; B3-B7; G5 joint satisfiability | as U3/U4 | 未供給 / この調査で経路未発見 |

## 2. First implemented unit (U6): `inClass_graphOf`, and why
Why: among the rows it is the only one whose statement closes from existing names (`InClass`, `WfG`, `graphOf`) with no new premise beyond the two explicit hypotheses; `hfo`, ReachSpans and the production link have no route found. It splits U3's `hin : InClass g B top = true` for `g := graphOf ds` into (i) a check on the names of `ds` and (ii) the rank condition. It supplies neither (i) nor (ii) for the production program, and it does not touch the rank computation.

File (new): `Tools/ShippingGen5NameKids6.lean`; check (new): `Tests/Gen5/NameKids6Check.lean`; two `lean_lib` entries in `lakefile.lean`. Imports: `Tools.ShippingGen5NameKids3`, `Tools.ShippingSrm15Graph`.
Namespace `Tools.ShippingGen5NameKids6`, `set_option autoImplicit false`. Opens: `Lean`, `Tools.ShippingMachineAuto (MachineData)`, `Tools.ShippingSrm15Graph (graphOf)`, `Tools.ShippingSrm7Rank (InClass declRank)`.

```
theorem inClass_graphOf {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true) :
    InClass (graphOf ds) B top = true
```
1 theorem, 0 new definitions. Its conclusion has the type of the `hin` binder of U3's `hself_all_reached` / `sepK_parent_all_reached` (with `g := graphOf ds`). Proof plan (not frozen): unfold `InClass`, `WfG`; rewrite `graphOf`, `List.map_map`, `List.length_map`; `simp [hnd, hr]`. Any type change found while proving is recorded here as an amendment before the Lean commit is offered.

What U6 does NOT show: that the production `ds` has pairwise distinct names (`hnd`); that the generated top has a rank within `B` (`hr`); `hfo`; ReachSpans; B3-B7; G5; the `machineShape?` ↔ `machineShapeF` link.

## 3. U6 checks (written from §2, not from the implementation)
* Expected TYPE: the theorem restated as an independent `def ExpInClassGraphOfF : Prop`, compared with the `Tests.Gen5.NameKidsCheck` comparator (`cmpTeleR`, `checkExpectedR`, `checkMutantR`): TYPE 1.
* Mutants, each well-typed (rejection is by signature/defeq, NOT a semantic counterexample); 4 single-point: (1) drop `hnd`; (2) drop `hr`; (3) `hnd` `= ds.length` → `≠ ds.length`; (4) conclusion `InClass (graphOf ds) B top` → `InClass (graphOf ds.reverse) B top`. No block mutant. Actual counts are reported with the counting rule in the header.
* Use-site `example`: `hself_all_reached (inClass_graphOf hnd hr) hg hsp` type-checks (type check only, not a semantic claim).
* Closure: U1-U5 walker (`reachWith`/`auditRoot`, fixtures `NameKidsFixture`): the theorem as root; negative 8 + clean 1; REACH 1. AXIOMS standard three only; no `sorry`/`native_decide`/`axiom`.
* After the Lean commit the Issue stays `doing` with "clean build は coder が実行". Builds are one at a time with `kjob lake build`.

## 4. Not done
No merge of other branches; no compiler/shared-definition change; no built file changed; no new TRUSTED/law. `hfo` supply, the rank half of InClass, ReachSpans, production link, (c), (d), G5, N1/G7/M5/FG: 未供給 / この調査で経路未発見.
