# DG-ACC freeze rev7 (issue `sparkle-gen5-dg-acc`): supplier table after A6c, and the next unit A7

**FOR REVIEW (docs only; no Lean for A7 is written until this is approved).** Rev1-rev6 unchanged. Base: `kjob/g5ac-r12` d9a894b2 (A6c approved; clean build `acv-d9a894b2`, exit 0, 737 jobs).
Header comment / rev6-table sync (A6c: build `acv-d9a894b2`, approved at d9a894b2) committed at 1502bea4, comment/docs only.

Tags: `[S]` source read (this worktree, or the named branch via `git show`); `[B]` built in this lineage. Nothing below was elaborated yet (statements only; the proof sketch is a plan, not a result).
Wording: "not supplied / no route found" = this survey did not find a supplier or route in the files read; never "impossible". MUTANTs are rejections by signature / defeq, not semantic counterexamples.
Conditional results are INTERMEDIATE, never completion. Maintained: `GetEnvFrame`, `ReaderRunsAt` and the start-world `ReadsAt` are inputs (not supplied); `hshape` is to be discharged by `readMachine_gates` at an integration SHA (ACC series is before S1). M5 / FG are not complete.

## 0. Survey of the DG-ACC rows still unsupplied

| row | premise (full type in) | existing lemma found (real name, location) | closes from it in this lineage? | state |
|---|---|---|---|---|
| C | `ClosesOfShape env₀ L Reach` (`Tools/ShippingGen5AccRoute.lean:42` `[B]`) | `Tools.ShippingMachineClosesData.letsClose_of_data` (`:177` `[B]`, needs `d.ok`, `d.shape.body = quote …`, `d.letsAliasOk`), `Tools.ShippingClosesSplit.machineCloses_iff` (`:50` `[B]`), `Tools.ShippingGen5Acc.machineClosesAtA_of_closes` (`Tools/ShippingGen5AccServed.lean:440` `[B]`), `K.genData₀_dataOf`, `dataOf₀_of_genData₀` (`Tools/ShippingGen5Acc.lean:58` `[B]`) | **yes, as a reduction**: `LetsClose` and (for `insts = []`) the whole `MachineCloses` follow from the three data facts; for `insts ≠ []` `CallsClose` stays a premise | **A7 below** |
| C′ | `CallsClose` for non-leaf reached names | `machineClosesAtA_of_pure` (`Tools/ShippingCallsCloseA.lean:138` `[S]`) needs `CallsPureA`, which is stated over real children (`ChildrenRealA`), i.e. the same induction as `AccServed0Stmt` | this survey did not find a non-circular route | not supplied / no route found |
| F | `d.ok`, `d.shape.body = quote …`, `d.shape = s` | `dataOfFrom_sound` / `dataOfAt_sound` (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:197,211`, conjuncts 1-3, owner dg-dataof) | not importable on this lineage; stated as a premise of its exact conjunct shape | integration obligation (owner dg-dataof) |
| L | `d.letsAliasOk = true` | this survey did not find a lemma giving it from `dataOfFrom` (`dataOfFrom_sound` does not list it) | no | not supplied / no route found |
| V | `ReachCover` data part (`genData₀ E = some g`) | DG-COVER, DG-SEM `genData₀` | owners dg-cover, dg-sem | not supplied (named only) |
| R | `ReadsSupplyAt` | DG-ENV U1/U2 | owner dg-env | not supplied (named only) |
| D | `DataOfShape K` | `dataOfAt_sound` conjunct 1 | integration obligation | named only |
| O | `OffRouteServes`, `GenSFacts` (`Tools/ShippingGen5AccGenP.lean:23`) | none found; DG-SEM | owner dg-sem | not supplied / no route found |

Rows V, R, D, O belong to other Issues (DG-COVER, DG-ENV, DG-DATAOF, DG-SEM); they are only named here and nothing is implemented for them.

## 1. Chosen unit: A7 `closesOfShape_of_data` (new file `Tools/ShippingGen5AccCloses.lean`, imports `Tools.ShippingGen5AccRoute`)

Reason: of the rows DG-ACC itself still owns, C is the only one where existing built lemmas (`letsClose_of_data`, `machineCloses_iff`, `machineClosesAtA_of_closes`) already reach the target `ClosesOfShape`, and the connection (reached name → `genData₀` → `dataOf₀` → `d` with `d.shape = shape` through `DataOfShape`) is a small pure transport nobody else owns.
It replaces the opaque premise `ClosesOfShape` of `accServed0_of_cover_gates` by named data facts (F, L) that other owners supply plus `CallsClose` for non-leaf names (C′), and it makes explicit that leaf names (`insts = []`) need no `CallsClose`. No new law, no TRUSTED boundary, no change to shared definitions / `T1Hyp` / FG.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingClosesSplit (CallsClose)

/-- The data facts the machine closing needs (conjuncts 2,3 of `dataOfFrom_sound`, plus `letsAliasOk`), for every reached name. -/
def ClosesData (K : AssignKit ι dom env₀) (Reach : Name → Prop) : Prop :=
  ∀ c d, Reach c → dataOf₀ K c = some d →
    d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.letsAliasOk = true

/-- `CallsClose` for the non-leaf reached names, at every admissible context. -/
def ClosesCalls (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c d, Reach c → dataOf₀ K c = some d → d.shape.insts ≠ [] →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      CallsClose mctx mref cctx cref c d.shape

theorem closesOfShape_of_data (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop)
    (hcov : ReachCover K Reach) (hDS : DataOfShape K)
    (hD : ClosesData K Reach) (hC : ClosesCalls K L Reach) : ClosesOfShape env₀ L Reach
```
Proof plan: for `c ci shape` with `hc`, `hf : env₀.find? c = some ci`, `hsh : machineShape? … = some shape`, `mctx cctx hA`: `hcov` gives `E g hE hg`; `dataOf₀_of_genData₀` gives `dataOf₀ K c = some (K.dOf g)`; unfolding `dataOf₀` with `hf`, `hsh` shows it equals `K.dataOf E se shape`, so `hDS` gives `(K.dOf g).shape = shape`; `hD` gives the three facts; `letsClose_of_data` gives `LetsClose`; `machineCloses_iff.mpr ⟨_, fun hne => hC …⟩` gives `MachineCloses` (the `insts ≠ []` hypothesis is rewritten along `d.shape = shape`); `machineClosesAtA_of_closes` finishes. (`machineClosesAtA_of_closes` takes `MachineCloses` at the run's `mctx mref cctx cref`; the context equality is by unification.)

Not claimed: `ClosesData` or `ClosesCalls` holds for any real name (F is a dg-dataof obligation at integration, L and C′ are unsupplied / no route found); `ReachCover`, `DataOfShape`, `ReadsSupplyAt`, `GenSFacts`, off-route; M5; FG. DG-ACC is not complete.

## 2. Check plan (`Tests/Gen5/AccClosesCheck.lean`, new)
Same requirements as A6c.
TYPE: independent `Expected…` for the 2 definitions' bodies and the theorem (written from §1 prose), `checkExpected` with `Tests.Gen3.ExpectedType`, positive control.
MUTANT (well-typed single change; signature/defeq rejection only): `ClosesData` without `letsAliasOk`; `ClosesData` without the body equation; `ClosesCalls` without `insts ≠ []`; `closesOfShape_of_data` without `hDS`; without `hcov`; without `hC`. Counts reported as measured with the rule.
CLOSURE: `closureReport` (unknown = fail; positive closure of the root, root self-judgement, helper value / helper type unknown controls + clean, `withoutModifyingEnv`); AXIOMS standard three only; no sorry in roots (isolated walker-control negatives counted and located); reported counts are the measured ones.
Build one target at a time in the Pod (`-c 2`, incremental); the Check is built on the committed tree; the Lean commit stays `doing` ("clean build is the coder's").

## 3. Not claimed
DG-ACC, M5, FG are not complete. Any decision needing a new law / TRUSTED / shared-definition change: none is needed by A7 (if `ClosesCalls` turned out to need one, that would go to a `decision` document, not be assumed).
