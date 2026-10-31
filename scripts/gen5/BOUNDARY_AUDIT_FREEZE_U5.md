# BOUNDARY-AUDIT freeze U5 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit`. Branch `kjob/g5ba-r10`, base `5ca8c374` (= U4 approved `39c565c4` + comment-only header sync; build `ba9v-39c565c4`, exit 0, 735 jobs). This file ADDS to `BOUNDARY_AUDIT_FREEZE*.md` (U1-U4); nothing there is withdrawn.
"Not found" means only that this survey did not find a supplier or a route; it does not say a row is impossible or underivable. Nothing here claims N1, G5, G7, M5, FG or Issue completion.
No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing or GenWF strengthening is proposed. No decision document is needed.

## 0. U4 sync (done, comment only, commit 5ca8c374)
Headers of `Tools/ShippingGen5NameKids4.lean` and `Tests/Gen5/NameKids4Check.lean` record the reviewed build ba9v-39c565c4. `MutHmemAll` turns all six existential variables (n sm ps ci senv ai) into `∀` at once; it is a quantifier-block mutant, not a single-binder change. MUTANT 7 = 4 single-point + 1 quantifier-block + 2 cross-statement controls.
Maintained: `hF` does not fix the witness of any actual run; production bridge (`machineShape?` ↔ `machineShapeF`), GraphAgrees / InClass / ReachSpans, N1 / G5 / G7 / M5 / FG are unsupplied.

## 1. Survey of the remaining unsupplied rows (existing names, full types)

| row | existing lemma in THIS tree | closes? |
|---|---|---|
| `GraphAgrees g Reach S` (`Tools.ShippingGen5NameKids3.GraphAgrees : CallGraph → (Name → Prop) → (Name → Option MachineShape) → Prop := ∀ c, Reach c → callees g c = (S c).map MachineShape.instTagged`) | `Tools.ShippingSrm15Graph.callees_graphOf (ds : List (Name × MachineData)) (c : Name) (d : MachineData) (h : FirstOcc ds c d) : callees (graphOf ds) c = some d.shape.instTagged`, with `graphOf ds := ds.map fun p => (p.1, p.2.shape.instTagged)`, `FirstOcc ds c d := ds.find? (fun p => p.1 == c) = some (c, d)` | **Yes, as a conditional theorem** with premise "every reached `c` has `d` with `FirstOcc ds c d` and `S c = some d.shape`". The link of `ds` to the production `P` / `Reach` / `S` was not found in this survey |
| `InClass g B top = true` | `Srm7Rank.InClass g B top := WfG g && (declRank g B top).isSome` (decidable) | 未供給 / この調査で経路未発見 (for the generated program) |
| `ReachSpans g top Reach` | none (converse of `ReachClosed`) | 未供給 / この調査で経路未発見 |
| production link `machineShape?` ↔ `machineShapeF`; (c) ordinary child name; B3-B7; G5 joint satisfiability | as U3/U4 | 未供給 / この調査で経路未発見 |

## 2. First implemented unit (U5): `graphAgrees_of_firstOcc`, and why
Why: it is the only remaining row whose statement closes entirely from existing names (`callees_graphOf`) with no new premise beyond the explicit `FirstOcc`/`S` agreement; InClass and ReachSpans have no route found. It turns U3's `hg` binder into the named premise `hfo`. It does NOT supply `hfo`.

File (new): `Tools/ShippingGen5NameKids5.lean`; check (new): `Tests/Gen5/NameKids5Check.lean`; two `lean_lib` entries in `lakefile.lean`. Imports: `Tools.ShippingGen5NameKids3`, `Tools.ShippingSrm15Graph`.
Namespace `Tools.ShippingGen5NameKids5`, `set_option autoImplicit false`. Opens: `Lean`, `Sparkle.Compiler.Elab (MachineShape)`, `Tools.ShippingSrm15Graph (graphOf FirstOcc callees_graphOf)`, `Tools.ShippingSrm7Rank (CallGraph callees)`, `Tools.ShippingGen5NameKids3 (GraphAgrees)`, and `MachineData` as in `Tools/ShippingSrm15Graph.lean` (the same opens that file uses).

```
theorem graphAgrees_of_firstOcc {ds : List (Name × MachineData)} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape) :
    GraphAgrees (graphOf ds) Reach S
```
1 theorem, 0 new definitions. Output has the type of the `hg` binder of U3's `sepK_parent_all_reached` / `hself_all_reached` (with `g := graphOf ds`). Proof plan (not frozen): intro c hc; obtain d, hfd, hS; rewrite `callees_graphOf ds c d hfd` and `hS`; `rfl`/`simp [Option.map]`. Any type change found while proving is recorded here as an amendment before the Lean commit is offered.

What U5 does NOT show: that the production program's declaration list `ds` and its `Reach`/`S` satisfy `hfo`; InClass; ReachSpans; B3-B7; G5; the `machineShape?` ↔ `machineShapeF` link.

## 3. U5 checks (written from §2, not from the implementation)
* Expected TYPE: the theorem restated as an independent `def ExpGraphAgreesF : Prop` and compared with the `Tests.Gen5.NameKidsCheck` comparator (`cmpTeleR`, `checkExpectedR`, `checkMutantR`): TYPE 1.
* Mutants, each well-typed (rejection is by signature/defeq, NOT a semantic counterexample); 4 single-point: (1) drop `Reach c →` in `hfo`; (2) `S c = some d.shape` → `S c = none`; (3) `∃ d` → `∀ d` in `hfo`; (4) conclusion `graphOf ds` → `graphOf ds.reverse`. No block mutant. Counts are reported as actual numbers with the counting rule in the header (MUTANT 4).
* Use-site `example`: `sepK_parent_all_reached hin (graphAgrees_of_firstOcc hfo) hsp hmem` type-checks (type check only, not a semantic claim).
* Closure: U1-U4 walker (`reachWith`/`auditRoot`, fixtures `NameKidsFixture`): the theorem as root; negative 8 + clean 1; REACH 1. AXIOMS: `[propext, Classical.choice, Quot.sound]` only; no `sorry`/`native_decide`/`axiom`.
* After the Lean commit the Issue stays `doing` with "clean build は coder が実行". Builds are one at a time with `kjob lake build`.

## 4. Not done
No merge of other branches; no compiler/shared-definition change; no built file changed; no new TRUSTED/law. InClass, ReachSpans, production link, (c), (d), G5, N1/G7/M5/FG: 未供給 / この調査で経路未発見.
