# DG-ACC freeze rev8 (issue `sparkle-gen5-dg-acc`): survey after A7, and the next unit A8

**FOR REVIEW (docs only; no Lean for A8 is written until this is approved).** Rev1-rev7 unchanged. Base: `kjob/g5ac-r14` c12df3ef (A7 approved; clean build `ac14v-c12df3ef`, exit 0, 725 jobs; freeze 419bc85c). Header / rev7-table sync to that build is committed at 70a43156 (comment/docs only).

Tags: `[S]` source read (this worktree, or the named branch via `git show`); `[B]` built in this lineage. Nothing below was elaborated (statements only; the proof sketch is a plan, not a result).
Wording: "not supplied / no route found" = this survey did not find a supplier or route in the files read; never "impossible". MUTANTs are rejections by signature / defeq, not semantic counterexamples.
Conditional results are INTERMEDIATE, never completion. Still inputs, not supplied: `ClosesData`, `ClosesCalls`, `ReachCover`, `DataOfShape`, `GetEnvFrame`, `ReaderRunsAt`, start-world `ReadsAt`, a real run. S1 integration-SHA re-verification remains. M5 / FG are not complete.

## 0. Survey of the rows still unsupplied

| row | premise | existing lemma found (real name, location) | closes from it in this lineage? | state |
|---|---|---|---|---|
| F1 | `DataOfShape K` (`Tools/ShippingGen5AccServed.lean:69` `[B]`) | `K.dataOf` is an abstract field of `AssignKit`; conjunct 1 of `dataOfAt_sound` / `dataOfFrom_sound` (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:197,211` `[S]`, owner dg-dataof) | not importable here; `K.dataOf` is not tied to `dataOfAt` in this lineage | A8 states the exact conjuncts as ONE premise `DataSound K` and derives `DataOfShape K` from it; the premise itself is dg-dataof's integration obligation |
| F2 | `d.ok`, body equation of `ClosesData` | conjuncts 2,3 of the same two lemmas `[S]` | same | A8 (from `DataSound K`) |
| L | `d.letsAliasOk = true` | `Tools.ShippingMachineClosesData.aliasOk_sound` (`:139` `[B]`) goes the other way (from `aliasOk = true`); `Tools.ShippingLetsAliasInv.machBindLet*_noAlias` (`[B]`) are about `MachLets` of the reader state, and that file states the link from reader `let` values to typed `d.letFields` is NOT proved | this survey did not find a route to `letsAliasOk = true` | not supplied / no route found (stays a premise) |
| C′ | `ClosesCalls` | `machineClosesAtA_of_pure` (`Tools/ShippingCallsCloseA.lean:138` `[S]`) needs `CallsPureA` over real children (same induction as `AccServedStmt`) | no non-circular route found | not supplied / no route found |
| V | `ReachCover` | DG-COVER, DG-SEM `genData₀` | owners dg-cover, dg-sem | named only |
| other | `ReadsSupplyAt`, `GenSFacts`, off-route, `GetEnvFrame`, `ReaderRunsAt`, start `ReadsAt` | DG-ENV, DG-SEM, DG-READKINDS | owners elsewhere | named only |

Rows V and "other" belong to other Issues (DG-COVER, DG-SEM, DG-ENV, DG-READKINDS, DG-DATAOF); only named here, nothing implemented for them. Rows C′ and L have no closing route in files read.

## 1. Chosen unit: A8 `ClosesData` / `DataOfShape` from one `DataSound` premise (new file `Tools/ShippingGen5AccDataSound.lean`, imports `Tools.ShippingGen5AccCloses`)

Reason: of the rows DG-ACC owns, F1+F2 are the only ones whose content is exactly stated by existing lemmas (conjuncts 1-3 of `dataOfAt_sound`), and the transport from "for all `K.dataOf` results" to "for reached names via `dataOf₀`" is small, pure, and owned by nobody else. A8 turns two premises (`DataOfShape K`, the F-part of `ClosesData`) into one named premise `DataSound K` with exactly dg-dataof's conjunct shape, leaving only `letsAliasOk` (L) as a separate premise. It supplies neither `DataSound` for the real `dataOf` nor L. No new law, no TRUSTED boundary, no change to shared definitions / `T1Hyp` / FG.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineClosesData

/-- Conjuncts 1-3 of `dataOfAt_sound` / `dataOfFrom_sound`, for the kit's `dataOf`. -/
def DataSound (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData),
    K.dataOf E se s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

theorem dataOfShape_of_sound (K : AssignKit ι dom env₀) (h : DataSound K) : DataOfShape K

theorem closesData_of_sound (K : AssignKit ι dom env₀) (Reach : Name → Prop) (h : DataSound K)
    (hL : ∀ c d, Reach c → dataOf₀ K c = some d → d.letsAliasOk = true) : ClosesData K Reach
```
(`ι`, `dom`, `env₀` are the section variables of `Tools/ShippingGen5Acc.lean` / `AccCloses.lean`; A8 declares them with `variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}` under `autoImplicit false`.)

Proof plan: `dataOfShape_of_sound`: `fun E se s d hd => (h E se s d hd).1`. `closesData_of_sound`: given `c d hc hd`, unfold `dataOf₀ K c = some d` (`Option.bind_eq_some_iff` twice) to `K.dataOf E (structEnv env₀) shape = some d`, apply `h` for `ok` and the body equation (conjuncts 2,3), `hL c d hc hd` for `letsAliasOk`.

Not claimed: `DataSound K` for any real kit (dg-dataof integration obligation; `K.dataOf` is not tied to `dataOfAt` here); `letsAliasOk` for any real name (L: not supplied / no route found); `ClosesCalls`, `ReachCover`, `ReadsSupplyAt`, `GenSFacts`, off-route; M5; FG. DG-ACC is not complete.

## 2. Check plan (`Tests/Gen5/AccDataSoundCheck.lean`, new)
Same requirements as A7.
TYPE: independent `Expected…` for `DataSound` body and both theorems (written from §1 prose), `checkExpected` with `Tests.Gen3.ExpectedType`, definition compared by body, positive control.
MUTANT (well-typed single change; signature/defeq rejection only): `DataSound` without the body-equation conjunct; `DataSound` without `d.ok`; `DataSound` with `d.shape = s` dropped; `closesData_of_sound` without `hL`; `closesData_of_sound` without `h`; `dataOfShape_of_sound` with `Reach`-restricted statement. Counts reported as measured with the rule.
CLOSURE: `closureReport` (unknown = fail; positive closure of roots, root self-judgement, helper value / helper type unknown controls + clean, `withoutModifyingEnv`; forbidden set and expected suppliers fixed, DataOf/SemGen units not reached); AXIOMS standard three only; no sorry in roots (isolated walker-control negatives counted and located); measured counts reported.
Build one target at a time in the Pod (`-c 2`, incremental), Check on the committed tree; Lean commit stays `doing` ("clean build is the coder's").

## 3. Not claimed / decisions
DG-ACC, M5, FG are not complete. A8 needs no new law / TRUSTED / shared-definition change; if it did, it would go to a `decision` document.
