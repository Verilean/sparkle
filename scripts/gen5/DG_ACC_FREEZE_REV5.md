# DG-ACC freeze rev5 (issue `sparkle-gen5-dg-acc`): supplier table for the premises left after A6a, and the next unit A6b

**FOR REVIEW (docs only; no Lean for A6b is written until this is approved).** Rev1-rev4 unchanged. Base: `kjob/g5ac-r8` da5a6106 (A6a approved; build `ac8v-da5a6106`, exit 0, 724 jobs);
header comment sync (A6a Check/Tools: SHA, build state, warning count 6, closure scope) committed at eb990da4, comment only.

Tags: `[S]` source read (this worktree, or the named branch via `git show`/`git grep`); `[B]` built in this lineage; `[E]` the statements below elaborate in a Pod scratch file
(`kjob lake env lean`, scratchpad, not committed; statements AND the proof elaborated, exit 0, axioms `propext, Classical.choice, Quot.sound`; the scratch is not an implementation).
Wording: "not supplied / no route found" = this survey did not find a supplier or route in the files read; never "impossible". MUTANTs are rejections by signature / defeq, not semantic counterexamples.
Conditional results are INTERMEDIATE, never completion. The closure audit of the Checks is `getUsedConstants`-based (constants mentioned by types and values); it is not an audit specific to raw projections.

## 0. Key finding of this survey

Every approved part that could supply a remaining A6a premise lives on a branch that is **not an ancestor** of this lineage (and the lineage is before S1, `T2Tie` does not elaborate here, so
`Tools.ShippingGen5EnvQ` and the files importing it cannot be imported). So none of the rows below can be *closed* inside this lineage by calling an approved part; what can be written here is the
**conditional reduction whose hypothesis has exactly the shape of the approved part's conclusion**, so that at integration the approved part is the supplier. This does not re-implement any other issue's row.

## 1. Supplier table (rows = the remaining premises of A6a; owner issue named; "approved part" with real name and branch)

| row | premise | approved part (name, location) | what it gives | gap this survey found | state in this lineage |
|---|---|---|---|---|---|
| G | `GatesNoneAt env₀ Reach` | `readMachine_gates` (`kjob/g5rk-r14:Tools/ShippingGen5ReadKindsU8.lean:53`, `[S]`; DG-READKINDS U8d, clean build `rk12v-f86cbdd7`) | from a successful `RunsTo (readMachine c false)`: `∃ ci env w1 w2`, a `getEnv` run `w→env,w1`, a `getConstInfo c` run `w1→ci,w2`, and both gate refusals at `GenEntry ci env` (`GenEntry ci env = entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)`, `kjob/g5rk-r14:Tools/Prototype/DGenProv.lean:29`) | (1) a `readMachine c false` run for every reached `c` (real-run tie / coverage; owner dg-readkinds, dg-cover): no supplier found. (2) `ReadsAt env₀` at the two read worlds (`hall`; owner dg-env). (3) U8d is not importable here. | **A6b below** is the transport from that shape to `GatesNoneAt` (uses `ci_of_readsAt`, `envR_of_readsAt`, `[B]` in `Tools/ShippingGen5Env.lean`). The premise stays unsupplied. |
| C | `ClosesOfShape env₀ L Reach` | `closes_of_data` (`Tools/ShippingMachineClosesData.lean:226`, `[B]`), `machineClosesAtA_of_closes` (A5b, `[B]`); `dataOfFrom_sound` conj. 2,3 (`kjob/g5do-r6`) for `d.ok` / body equation | no-call case conditional on `d.ok`, body equation, `d.letsOk = true` | existence of `d` (= `ReachCover` data part); `CallsClose` supplier for the calls case (`Tools/ShippingClosesSplit.lean:40`): none found | not supplied / no route found (a no-call sub-unit is a later candidate, conditional on the cover) |
| V | `ReachCover K Reach` | DG-COVER Cover3-6 (`kjob/g5cv-r13`: `rowA2/3/B1_of_inv`, `rowC_of_reader_ok`, `shapeAgree_of_production/_sides`, `fullInv_reachC`, `reserved_reachC`); DG-DATAOF `dataOfFrom_dims`/`dataOfAt_dims` (row 6b) | `ShapeAgree` rows *given* a reader run / reader-state invariant, and projections of a given `dataOfFrom = some` | existence `entry₀ env₀ c = some E` and `K.genData₀ E = some g` for every reached `c` (`dataOfAt … = some _`, `GenWF`): DG-DATAOF §11.2 rows 1-6,8 open; no run supplier | not supplied / no route found (owners dg-dataof, dg-readertrace, dg-readkinds, dg-cover) |
| R | `ReadsSupplyAt env₀ L Reach` | DG-ENV U1 (a14f2479: `ReadsAt` E1-E6, `machineDefinesR_of_env`, `[B]` here), U2 (in progress) | `ReadsAt` lemmas; strengthened `L'` in `Tools/ShippingGen5AccReads.lean` `[B]` | FG's `L` (non-strengthened) and `GetEnvFrame`: not supplied; EnvQ agreement is source-text only (rev4 §4) | not supplied (owner dg-env) |
| D | `DataOfShape K` | `dataOfAt_sound` conj. 1 (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:211`) with `K.dataOf := dataOfAt lvl` | the premise at integration | not importable here | integration obligation (A6) |
| E | `hcl` / reach closure | `ReachEdge.edge` (`Tools/ShippingGen5Acc.lean:201-203`, `[B]`); reach U2/U5 (names read in rev4 §2; not re-surveyed to a new result) | closure under static ordinary edges for `Reach := ReachEdge K Top` | arbitrary `Reach`: hypothesis | supplied for `ReachEdge K Top`; otherwise premise |
| O | `OffRouteServes`, `GenSFacts` | none found (O); DG-SEM pieces (GenSFacts, owner dg-sem) | — | — | not supplied / no route found; owned by M4 generalisation / dg-sem, not implemented here |

## 2. First unit to implement: A6b `gatesNoneAt_of_gateRunsAt` (new file `Tools/ShippingGen5AccGates.lean`, imports `Tools.ShippingGen5AccRoute`)

Reason: it is the only remaining row where (a) the approved supplier's conclusion shape is fixed and known (`readMachine_gates`), (b) the transport to `env₀` uses only parts already built in this lineage, and
(c) no other issue owns the transport (DG-READKINDS U8e transports with `hall` at every world; this is the per-world form needed by `MachineDefinesR`/`GatesNoneAt`). It makes the rev4 premise `GatesNoneAt`
re-attributable to two named, separately owned items (the reader runs + two `ReadsAt` worlds). It does **not** supply them.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
open Tools.ShippingGen5Env (ReadsAt ci_of_readsAt envR_of_readsAt)

/-- For every reached name found in `env₀`: a `getEnv` run and a `getConstInfo` run at worlds where the Core environment agrees with `env₀`
(`ReadsAt`), with both gate refusals at the entry built from THOSE run results (the shape of the conclusion of `readMachine_gates`). -/
def GateRunsAt (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ wE envR wE' w1 ci w2,
      ReadsAt env₀ cref wE ∧ ReadsAt env₀ cref w1 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none

theorem gatesNoneAt_of_gateRunsAt {env₀ : Environment} (mctx : Meta.Context)
    (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (Reach : Name → Prop) (h : GateRunsAt env₀ mctx mref cctx cref Reach) : GatesNoneAt env₀ Reach
```
Proof (elaborated in scratch `[E]`): `ci' = ci₀` by `ci_of_readsAt` and `find?` uniqueness; `envR_of_readsAt` gives `instancePredicate/userInliner/structEnv envR = … env₀`; rewrite; done.

At integration (not here): `readMachine_gates hrun` after `unfold GenEntry` gives the `∃` body of `GateRunsAt` except the two `ReadsAt` facts, which come from DG-ENV; the `hrun` per reached name is the real-run tie / coverage (unsupplied).
Not claimed: `GateRunsAt` supplied; any `readMachine` run exists for any reached name; `hall`; the real-run tie; `ReachCover`; `ClosesOfShape`; `ReadsSupplyAt`; `DataOfShape`; off-route; M5; FG. No new law / TRUSTED / FG change / `T1Hyp` change / shared or compiler edit.

## 3. Check plan (`Tests/Gen5/AccGatesCheck.lean`, new)
TYPE: independent `Expected…` for the definition body and the theorem (written from §2 prose, not copied), `checkExpected` binder by binder, same reducible comparator `Tests.Gen3.ExpectedType`, positive control.
MUTANT (well-typed single change, signature/defeq rejection only): `GateRunsAt` without the mixed conjunct; without `ReadsAt` at `w1`; without `ReadsAt` at `wE`; `gatesNoneAt_of_gateRunsAt` without `h`; counts reported as measured with the classification rule.
CLOSURE: `closureReport` (unknown = fail; roots in `seen`; root / helper value / helper-type unknown controls + clean, `withoutModifyingEnv`); AXIOMS standard three; sorry absent from roots (isolated negative fixtures counted and located).
Build one target at a time in the Pod; the Check is built on the tree that is committed; the Lean commit stays `doing` ("clean build is the coder's").

## 4. Not claimed
DG-ACC, M5, FG are not complete. EnvQ agreement remains a source-text comparison until the integration SHA (rev4 §4). This lineage is before S1.

## 5. Wording sync at implementation (A6b; no change of types)
- `GateRunsAt` drops `wE' = w1`, so it is NOT identical in shape to the conclusion of `readMachine_gates`; it is a weaker sufficient interface that can be built from that conclusion.
  At integration the obligation is to supply the linked witness of the SAME reader run (the `getEnv` run ending where the `getConstInfo` run starts), not an unlinked pair.
- That the approved parts (`readMachine_gates`, Cover3-6, `dataOfFrom_sound`, reach, DG-ENV) are on branches that are not ancestors is a limit of the current un-integrated checkout, not a statement that they can never be imported.
- Implemented as frozen: `Tools/ShippingGen5AccGates.lean` (definition 1, theorem 1), `Tests/Gen5/AccGatesCheck.lean`. Pod build at 5b542e30: Tools 722 jobs, Check 725 jobs, exit 0. Clean issue-linked build ac10v-00f1b849 exit 0, 725 jobs, approved at 00f1b849.
  Check: TYPE 2 (syntactic) / MUTANT 4 (signature/defeq rejections, not semantic counterexamples) / AXIOMS 2 standard three / CLOSURE 7808 constants, unknown 0 / sorry only in the intended walker-control negatives (6 warnings: 3 in `AccCheck.lean:238`, 3 in `AccGatesCheck.lean:96`).
- Not a supply of: any reader run, `ReadsAt`, `ReachCover`, `ClosesOfShape`, `ReadsSupplyAt`, `DataOfShape`, off-route, `GenSFacts`. Not DG-ACC / M5 / FG completion.
