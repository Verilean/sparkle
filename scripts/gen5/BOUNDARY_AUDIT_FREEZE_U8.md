# BOUNDARY-AUDIT freeze U8 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit`. Branch `kjob/g5ba-r16`, base `d3cd9c6d` (= U7 approved `3f5bcb2e` + comment-only header sync to build `ba15v-3f5bcb2e`, exit 0, 723 jobs). This file ADDS to `BOUNDARY_AUDIT_FREEZE*.md` (U1-U7); nothing there is withdrawn.
"Not found" means only that this survey did not find a supplier or a route; it does not say a row is impossible or underivable. Nothing here claims N1, G5, G7, M5, FG or Issue completion.
No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing or GenWF strengthening is proposed. No decision document is needed.

## 0. U7 sync (done, comment only, commit d3cd9c6d)
Headers of `Tools/ShippingGen5NameKids7.lean` and `Tests/Gen5/NameKids7Check.lean` record the reviewed build ba15v-3f5bcb2e. `MutSNone` replaces `S` in BOTH the premise and the conclusion (a two-place change); the Check header and comments now count MUTANT 4 as 3 single-change (MutNoHg, MutHgTrue, MutConclSpans) + 1 two-place (MutSNone). Rejection is by signature/defeq, not a semantic counterexample.
Maintained: the supply of `hg`, its non-vacuity, production `Reach` / `GraphAgrees` / `hnd` / `hr` / `hfo`, FG, integrated SHA verification are unsupplied.

## 1. Survey of the remaining rows (existing names, full types)

| row | what this survey found in THIS tree | closes? |
|---|---|---|
| `hg : GraphAgrees g Reach S` for `g = graphOf ds` | U5 `graphAgrees_of_firstOcc` (Tools/ShippingGen5NameKids5.lean): `(hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape) → GraphAgrees (graphOf ds) Reach S`. `FirstOcc` is stated in `Tools.ShippingSrm15Graph`; no lemma was found that derives `FirstOcc ds c d` from membership `(c, d) ∈ ds` plus name distinctness | **Yes, partly** (§2): the `FirstOcc` conjunct of `hfo` is replaced by plain membership, using the SAME `hnd` premise as U6 |
| production `hnd` | not supplied (U7 §1) | 未供給 / この調査で辿った候補経路では未発見 |
| production `hr` | not supplied (U7 §1) | 未供給 / この調査で辿った候補経路では未発見 |
| membership `(c, d) ∈ ds ∧ S c = some d.shape` for reached `c` | `GraphCovers` / `DefsProv` (Tools.ShippingSrm15Graph) are stated premises; `DefsProv` says `MachineDefines … p.1 p.2.shape` for listed `p`, which is about listed entries, not about `S`. No link from the production `Reach` / `S` to `ds` was found | 未供給 / この調査で辿った候補経路では未発見 |
| ReachSpans for the production `Reach`; production bridge `machineShape?` ↔ `machineShapeF`; (c); B3-B7; G5; FG | as U3-U7 | 未供給 / この調査で辿った候補経路では未発見 |

## 2. First implemented unit (U8): `graphAgrees_of_mem`, and why
Why: it is the only row of this survey that closes from existing names plus a self-contained list argument. It makes U5 and U6 share ONE name-distinctness premise `hnd` (U6 already takes it for `InClass`): with `hnd`, the unit-5 premise `hfo` weakens from "first occurrence" to "membership in `ds`", which is the form a provenance statement (`DefsProv` / `GraphCovers` style) naturally gives. LIMIT (stated plainly): `hnd` and the membership premise are both still premises; this unit does NOT supply `hnd`, does NOT link the production `Reach`/`S` to `ds`, and is conditional (no instance of its premises is constructed, so it is not evidence of non-vacuity).

File (new): `Tools/ShippingGen5NameKids8.lean`; check (new): `Tests/Gen5/NameKids8Check.lean`; two `lean_lib` entries in `lakefile.lean`. Imports: `Tools.ShippingGen5NameKids5` (which imports `Tools.ShippingGen5NameKids3` and `Tools.ShippingSrm15Graph`).
Namespace `Tools.ShippingGen5NameKids8`, `set_option autoImplicit false`. Opens: `Lean`, `Sparkle.Compiler.Elab (MachineShape)`, `Tools.ShippingMachineAuto (MachineData)`, `Tools.ShippingSrm15Graph (graphOf)`, `Tools.ShippingGen5NameKids3 (GraphAgrees)`.

```
theorem graphAgrees_of_mem {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hmem : ∀ c, Reach c → ∃ d : MachineData, (c, d) ∈ ds ∧ S c = some d.shape) :
    GraphAgrees (graphOf ds) Reach S
```
The `hnd` binder is character-for-character the `hnd` of `inClass_graphOf` (U6). Unfolded conclusion: `∀ c, Reach c → callees (graphOf ds) c = (S c).map MachineShape.instTagged`.
1 theorem, 0 new definitions (auxiliary facts are `private theorem`s inside the file: (a) `(l.eraseDups).length ≤ l.length` for `l : List Name`; (b) `hnd` ⇒ `(ds.map Prod.fst).Nodup`; (c) Nodup names and `(c, d) ∈ ds` ⇒ `FirstOcc ds c d`). Proof plan (not frozen): (a) by strong induction on length with `List.eraseDups_cons` and `List.length_filter_le`; (b) by induction on `ds` using `List.eraseDups_cons`, equality of lengths forcing the head to be absent from the tail; (c) by induction on `ds`; then `graphAgrees_of_firstOcc` (U5). Name has `LawfulBEq` (Init/Meta/Defs.lean). If the proof needs a different shape (e.g. the Nodup route is replaced by a direct induction), the stated type above does not change; any type change is recorded here as an amendment before the Lean commit is offered.

What U8 does NOT show: `hnd` for the production `ds`; `hr`; membership of reached declarations in `ds`; that the production `Reach` is `OrdPath g top`; ReachSpans for the production `Reach`; the `machineShape?` ↔ `machineShapeF` link; B3-B7; G5; N1/G7/M5/FG.

## 3. U8 checks (written from §2, not from the implementation)
* Expected TYPE: the theorem restated as an independent `def ExpGraphAgreesOfMemF : Prop` (using the def names `GraphAgrees`, as in U7, because the reducible comparator does not unfold), compared with the `Tests.Gen5.NameKidsCheck` comparator (`checkExpectedR`, `checkMutantR`): TYPE 1.
* Mutants, each well-typed (rejection is by signature/defeq, NOT a semantic counterexample). Counts are reported by kind, as measured: single-change mutants vs multi-place mutants. Planned: 4 single-change: (1) drop `hnd`; (2) in `hnd`, `= ds.length` → `≤ ds.length`; (3) conclusion `GraphAgrees (graphOf ds) Reach S` → `GraphAgrees (graphOf ds) (fun _ => True) S`; (4) in `hmem`, `S c = some d.shape` → `S c = none`; plus 1 multi-place: `S` replaced by `fun _ => none` in `hmem` and the conclusion (reported separately, not as single-point). The measured number per kind is reported in the Check header; if the comparator accepts one, it is reported as accepted, not hidden. No block mutant. Actual counts are reported with the counting rule in the header.
* Use-site `example` (type check only, not a semantic claim): `inClass_graphOf hnd hr` (U6) and `graphAgrees_of_mem hnd hmem` are stated with the SAME `hnd`, and combined with `hself_all_reached` to give the U3 consumer output for `Reach := OrdPath (graphOf ds) top` (using `reachClosed_ordPath` is not needed here; `ReachSpans` is `fun _ h => h`). This type-checks that the premises of U3/U6/U8 line up; it does not supply any of them.
* Closure: U1-U7 walker (`reachWith`/`auditRoot`, fixtures `NameKidsFixture`): the theorem as root; negative 8 + clean 1; REACH 1. AXIOMS standard three only; no `sorry`/`native_decide`/`axiom`.
* After the Lean commit the Issue stays `doing` with "clean build は coder が実行". Builds are one at a time with `kjob lake build`.

## 4. Not done
No merge of other branches; no compiler/shared-definition change; no built file changed; no new TRUSTED/law. Production `hnd` / `hr`, membership of reached declarations in `ds`, ReachSpans for the production `Reach`, production link, (c), (d), G5, N1/G7/M5/FG: 未供給 / この調査で辿った候補経路では未発見.
