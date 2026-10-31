# BOUNDARY-AUDIT freeze U7 (docs only; Lean follows after approval)

Issue: `sparkle-gen5-boundary-audit`. Branch `kjob/g5ba-r14`, base `7ed4a5c8` (= U6 approved `b07cfcec` + comment-only header sync to build `ba13v-b07cfcec`, exit 0, 724 jobs). This file ADDS to `BOUNDARY_AUDIT_FREEZE*.md` (U1-U6); nothing there is withdrawn.
"Not found" means only that this survey did not find a supplier or a route; it does not say a row is impossible or underivable. Nothing here claims N1, G5, G7, M5, FG or Issue completion.
No new TRUSTED boundary, law, compiler/shared-definition edit, FG narrowing or GenWF strengthening is proposed. No decision document is needed.

## 0. U6 sync (done, comment only, commit 7ed4a5c8)
Headers of `Tools/ShippingGen5NameKids6.lean` and `Tests/Gen5/NameKids6Check.lean` record the reviewed build ba13v-b07cfcec (MUTANT 4 are single-point; rejection is by signature/defeq, not a semantic counterexample).
Maintained: production `hnd` / `hr`, name uniqueness, `hfo`, ReachSpans, production bridge, N1 / G5 / G7 / M5 / FG are unsupplied.

## 1. Survey of the remaining rows (existing names, full types)

| row | what this survey found in THIS tree | closes? |
|---|---|---|
| production `hnd : (ds.map Prod.fst).eraseDups.length = ds.length` | no lemma or hypothesis about pairwise distinct names of the production `ds` (`GraphCovers`, `DefsProv` in `Tools.ShippingSrm15Graph` do not mention it; `firstOcc_unique` is about `FirstOcc`, not about `ds`) | 未供給 / この調査で辿った候補経路では未発見 |
| production `hr : (declRank (graphOf ds) B top).isSome = true` | `rank_of_reach`, `rank_of_ordEdge` propagate a rank from `top` to its descendants; no theorem producing a rank for `top` of a generated program | 未供給 / この調査で辿った候補経路では未発見 |
| `hfo` (production `ds` ↔ `Reach` / `S`) | `T1Hyp` (Tools/ShippingGen2Defs.lean:201) takes `Reach` as a free parameter; `GraphCovers` / `DefsProv` are stated premises. No link from the production `ds` to `Reach` / `S` found | 未供給 / この調査で辿った候補経路では未発見 |
| `ReachSpans g top Reach` for the production `Reach` | `Reach` is a free parameter of `T1Hyp`; `T1Hyp.closed` is closure only (the converse is not a field). No lemma that the production `Reach` is minimal was found | 未供給 / この調査で辿った候補経路では未発見 |
| `ReachClosed` / `ReachSpans` for the REACHABILITY-DEFINED set `OrdPath g top` | `ReachSpans g top (OrdPath g top)` is `fun _ h => h`. `ReachClosed (OrdPath g top) S` follows from `GraphAgrees g (OrdPath g top) S` with `instTagged_getElem` (Tools.ShippingInstTagged), `List.getElem_mem`, `OrdPath.step`, and the `memKey` / `child?` case split already used privately in `Tools.ShippingGen5NameKids3` | **Yes** (§2), for the set defined as `OrdPath`, not for the production `Reach` |
| production link `machineShape?` ↔ `machineShapeF`; (c); B3-B7; G5 | as U3/U4 | 未供給 / この調査で辿った候補経路では未発見 |

## 2. First implemented unit (U7): `reachClosed_ordPath`, and why
Why: it is the only row of the survey that closes from existing names with a single explicit hypothesis (`GraphAgrees`). It shows that the two U3 premises `ReachClosed` and `ReachSpans` are jointly satisfiable for the set `OrdPath g top` (the least set containing `top` and closed under ordinary edges of `g`), so the pair of premises used by `hself_all_reached` / `sepK_parent_all_reached` is not vacuous or contradictory. LIMIT (stated plainly): this does NOT show that the production `Reach` of `T1Hyp` equals or is contained in `OrdPath g top`; that link was not found, so ReachSpans for the production `Reach` stays unsupplied.

File (new): `Tools/ShippingGen5NameKids7.lean`; check (new): `Tests/Gen5/NameKids7Check.lean`; two `lean_lib` entries in `lakefile.lean`. Imports: `Tools.ShippingGen5NameKids3`.
Namespace `Tools.ShippingGen5NameKids7`, `set_option autoImplicit false`. Opens: `Lean (Name)`, `Sparkle.Compiler.Elab (MachineShape)`, `Tools.ShippingSrm7Rank (CallGraph)`, `Tools.ShippingGen5NameKids3 (GraphAgrees ReachClosed ReachSpans OrdPath OrdEdge)`.

```
theorem reachClosed_ordPath {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (OrdPath g top) S) :
    ReachClosed (OrdPath g top) S
```
Unfolded for review (what the conclusion says): `∀ c, OrdPath g top c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length), (sp.instOrigins.getD k InstOrigin.ord).child? = none → OrdPath g top (sp.insts[k]'hk).1`.
1 theorem, 0 new definitions. Proof plan (not frozen): from `hg c hc` and `S c = some sp` get `callees g c = some sp.instTagged`; the entry `((sp.insts[k]).1, originAt sp k)` is `sp.instTagged[k]` (`instTagged_getElem`), hence a member; `child? = none` gives `memKey (originAt sp k) = none` (case split on `InstOrigin`); build `OrdEdge g c (sp.insts[k]).1` and apply `OrdPath.step`. Any type change found while proving is recorded here as an amendment before the Lean commit is offered.

What U7 does NOT show: that the production `Reach` is `OrdPath g top`; `GraphAgrees` for any production set; `hnd`; `hr`; `hfo`; ReachSpans for the production `Reach`; B3-B7; G5; the `machineShape?` ↔ `machineShapeF` link.

## 3. U7 checks (written from §2, not from the implementation)
* Expected TYPE: the theorem restated as an independent `def ExpReachClosedOrdPathF : Prop`, compared with the `Tests.Gen5.NameKidsCheck` comparator (`cmpTeleR`, `checkExpectedR`, `checkMutantR`): TYPE 1.
* Mutants, each well-typed (rejection is by signature/defeq, NOT a semantic counterexample); 4 single-point: (1) drop `hg`; (2) `GraphAgrees g (OrdPath g top) S` → `GraphAgrees g (fun _ => True) S`; (3) conclusion `ReachClosed (OrdPath g top) S` → `ReachSpans g top (OrdPath g top)`; (4) `S` replaced by `fun _ => none` in both hypothesis and conclusion. No block mutant. Actual counts are reported with the counting rule in the header.
* Use-site `example` (type check only, not a semantic claim): `hself_all_reached hin hg (fun _ h => h)` with `Reach := OrdPath g top` is combined with `reachClosed_ordPath` so the premises `ReachClosed`/`ReachSpans` are both discharged for that set.
* Closure: U1-U6 walker (`reachWith`/`auditRoot`, fixtures `NameKidsFixture`): the theorem as root; negative 8 + clean 1; REACH 1. AXIOMS standard three only; no `sorry`/`native_decide`/`axiom`.
* After the Lean commit the Issue stays `doing` with "clean build は coder が実行". Builds are one at a time with `kjob lake build`.

## 4. Not done
No merge of other branches; no compiler/shared-definition change; no built file changed; no new TRUSTED/law. Production `hnd` / `hr`, `hfo`, ReachSpans for the production `Reach`, production link, (c), (d), G5, N1/G7/M5/FG: 未供給 / この調査で辿った候補経路では未発見.
