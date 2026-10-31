# DG-ACC freeze rev9 (issue `sparkle-gen5-dg-acc`): survey after A8, and the next unit A9

**FOR REVIEW (docs only; no Lean for A9 is written until this is approved).** Rev1-rev8 unchanged. Base: `kjob/g5ac-r16` 467c093b (A8 approved; clean build `ac16v-467c093b`, exit 0, 726 jobs; freeze 17d6ba0e). Header / rev8 sync (build name; `MutShapeReach` is a COMPOUND mutant, Reach binder added and conclusion changed, counted apart from the 5 single-change mutants) is committed at 66177c58 (comment/docs only).

Tags: `[S]` source read (this worktree, or the named branch via `git show`); `[B]` built in this lineage. Nothing below was elaborated (statements only; the proof sketch is a plan, not a result).
Wording: "not supplied / no route found" = the candidate routes followed in this survey did not reach a supplier; never "impossible". MUTANTs are rejections by signature / defeq, not semantic counterexamples.
Conditional results are INTERMEDIATE, never completion. Still inputs, not supplied: `DataSound` for a real kit, `K.dataOf = dataOfAt`, `letsAliasOk` (L), `ClosesCalls` (C′), `ReachCover`, `GetEnvFrame`, `ReaderRunsAt`, start-world `ReadsAt`, a real run. S1 integration-SHA re-verification remains. M5 / FG are not complete.

## 0. Survey of the rows still unsupplied (after A8)

| row | premise | existing lemma followed (real name, location) | closes in this lineage? | state |
|---|---|---|---|---|
| D | `DataSound K` for a real kit | `Tools.ShippingGen5DataOf.dataOfAt_sound` / `dataOfFrom_sound` (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:197,211` `[S]`); `kjob/g5do-r6` is not an ancestor of this branch and the `Tools/ShippingGen5DataOf*` files are not in this tree (`ls Tools`) | not importable here without a merge/integration (outside this Issue) | owner dg-dataof; the candidate route (import + instantiate) is an integration step, not available on this base |
| D′ | `K.dataOf = dataOfAt lvl` (kit agreement) | `AssignKit.dataOf` is an abstract field (`Tools/ShippingGen5Acc.lean:33` `[B]`); `genData₀_dataOf` (`:41`) constrains only `genData₀` results | the agreement itself: a field of whichever kit is built (dg-dataof / dg-sem); the transport from agreement + a spec for the agreed function to `DataSound` is small, pure, and is stated nowhere yet | **A9 (below)** |
| L | `d.letsAliasOk = true` | `Tools.ShippingLetsAliasInv` (`Tools/ShippingLetsAliasInv.lean` `[B]`): `NoLetAlias` and `machClose_bvar` for the four total `machBindLet*` functions; its header lists as NOT proved the in-range premise for the `partial` readers and the link from reader `let` values to typed `d.letFields` | candidate route (reader `let`s -> `d.letFields`) not reached: that link is stated as unproved in the file itself | not supplied / no route found by the path followed |
| C′ | `ClosesCalls` | `machineClosesAtA_of_pure` (`Tools/ShippingCallsCloseA.lean:138` `[S]`) needs `CallsPureA` over real children (same induction as `AccServedStmt`) | the candidate path is circular with `AccServedStmt` | not supplied / no route found by the path followed |
| V | `ReachCover K Reach` (`∃ E g, entry₀ … ∧ genData₀ E = some g`, `Tools/ShippingGen5AccServed.lean` `[B]`) | DG-COVER, DG-SEM `genData₀` | owners dg-cover, dg-sem | named only |
| other | `ReadsSupplyAt`, `GenSFacts`, off-route, `GetEnvFrame`, `ReaderRunsAt`, start `ReadsAt`, rows 1-8 of `DG_DATAOF_FREEZE.md` rev3 §11.2 (coverage of `dataOfAt`) | DG-ENV, DG-SEM, DG-READKINDS, DG-DATAOF | owners elsewhere | named only |

## 1. Chosen unit: A9 `DataSound` from kit agreement with a specified function (new file `Tools/ShippingGen5AccDataAgree.lean`, imports `Tools.ShippingGen5AccDataSound`)

Reason: of the rows listed, D′ is the only one where a reusable piece is DG-ACC's to state and is closeable from names in this tree. It splits the dg-dataof integration obligation `DataSound K` into two named parts: (i) a spec `DataSoundAt f` for a plain function `f` (exactly the shape of conjuncts 1-3 of `dataOfAt_sound lvl`, which dg-dataof proves for `f := dataOfAt lvl`), and (ii) the agreement `KitAgrees K f` (the kit's `dataOf` is `f`). It does NOT supply (i) or (ii) for any real function or kit. The gain is small and honest: the premise at the integration point becomes two statements with different owners instead of one, and A8's `closesData_of_sound` / `dataOfShape_of_sound` compose with it. No new law, no TRUSTED boundary, no change to shared definitions / `T1Hyp` / FG.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingUnifiedSource (quote)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

/-- Conjuncts 1-3 of `dataOfAt_sound lvl`, for an arbitrary function `f`. -/
def DataSoundAt (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData),
    f E se s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

/-- The kit's `dataOf` is `f` (pointwise). -/
def KitAgrees (K : AssignKit ι dom env₀)
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape), K.dataOf E se s = f E se s

theorem dataSound_of_agree (K : AssignKit ι dom env₀)
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (hf : DataSoundAt f) (hK : KitAgrees K f) : DataSound K
```
(Section variables as in A8, under `autoImplicit false`.)

Proof plan: `fun E se s d hd => hf E se s d (by rw [← hK E se s]; exact hd)`.

Integration use (NOT done here): with `f := fun E se s => Tools.ShippingGen5DataOf.dataOfAt lvl E se s` and `hf` from `dataOfAt_sound lvl` (dropping its 4th conjunct), `dataSound_of_agree` gives `DataSound K` once a kit with `KitAgrees K (dataOfAt lvl)` exists; then A8 gives `DataOfShape K` and `ClosesData K Reach` (with L). Both the import of the DataOf modules and the kit are owned elsewhere (dg-dataof, dg-sem).

Not claimed: `DataSoundAt` for any named function; `KitAgrees` for any kit; `K.dataOf = dataOfAt`; L; C′; `ReachCover`; `ReadsSupplyAt`; `GenSFacts`; off-route; real run; M5; FG. DG-ACC is not complete.

## 2. Check plan (`Tests/Gen5/AccDataAgreeCheck.lean`, new)
Same requirements as A8.
TYPE: independent `Expected…` for `DataSoundAt` (body), `KitAgrees` (body) and the theorem, `checkExpected` with `Tests.Gen3.ExpectedType`, definitions compared by body.
MUTANT (signature/defeq rejection only; reported as measured, SINGLE and COMPOUND counted separately): single: `DataSoundAt` without the body-equation conjunct; `DataSoundAt` without `d.ok`; `KitAgrees` with the equation flipped (`f … = K.dataOf …`); theorem without `hf`; theorem without `hK`. Compound (more than one place changed): theorem conclusion changed to `DataOfShape K` together with `hf` weakened to the shape conjunct. Counts of each class are reported from the run, not predicted.
CLOSURE: `closureReport` (unknown = fail; positive closure of roots, root self-judgement, helper value / helper type unknown controls + clean, `withoutModifyingEnv`; forbidden set `sorryAx / ofReduceBool / trustCompiler` and expected suppliers fixed (`DataSound`, `KitAgrees`, `DataSoundAt`), DataOf/SemGen units not reached); AXIOMS standard three only; no sorry in roots (isolated walker-control negatives counted and located).
Build one target at a time in the Pod (`-c 2`, incremental), Check on the committed tree; Lean commit stays `doing` ("clean build is the coder's").

## 3. Not claimed / decisions
DG-ACC, M5, FG are not complete. A9 needs no new law / TRUSTED / shared-definition change; if it did, it would go to a `decision` document.
