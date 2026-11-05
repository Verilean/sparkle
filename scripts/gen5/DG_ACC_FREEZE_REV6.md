# DG-ACC freeze rev6 (issue `sparkle-gen5-dg-acc`): supplier table after A6b, and the next unit A6c

**FOR REVIEW (docs only; no Lean for A6c is written until this is approved).** Rev1-rev5 unchanged. Base: `kjob/g5ac-r10` 00f1b849 (A6b approved; clean build `ac10v-00f1b849`, exit 0, 725 jobs).
Header comment sync (A6b Tools/Check/rev5: build `ac10v-00f1b849`, approved at 00f1b849) committed at d53449d8, comment only.

Tags: `[S]` source read (this worktree, or the named branch via `git show`); `[B]` built in this lineage. Nothing below was elaborated yet (statements only; the proof sketch is a plan, not a result).
Wording: "not supplied / no route found" = this survey did not find a supplier or route in the files read; never "impossible". MUTANTs are rejections by signature / defeq, not semantic counterexamples.
Conditional results are INTERMEDIATE, never completion.

## 0. Survey result (rows remaining after A6b)

The approved parts are on branches that are not ancestors of this lineage (`kjob/g5rk-r14`, `kjob/g5cv-r13`, `kjob/g5do-r6`, DG-ENV U2); this is a limit of the un-integrated checkout, not an import impossibility in general.
`readMachine`, `Read` (`Tools/ShippingMachineCommand.lean:390,440` `[S][B]`), `GenEntry` (`Tools/Prototype/DGenProv.lean:29`, `[S]`, in tree), `GetEnvFrame` / `EnvFrame` (`Tools/ShippingEnvSnapshot.lean:43,62` `[B]`) and `ReadsAt.of_frame` (E3, `Tools/ShippingGen5Env.lean:47` `[B]`) ARE in this lineage.
`readMachine_gates` itself is not (`kjob/g5rk-r14:Tools/ShippingGen5ReadKindsU8.lean:53`, owner dg-readkinds, U8d): it is NOT re-implemented here.

| row | premise | approved part (name, location) | closable in this lineage by calling it? | state |
|---|---|---|---|---|
| G1 | `GateRunsAt` (A6b) from ONE reader run | `readMachine_gates` (dg-readkinds U8d) gives the linked `getEnv`/`getConstInfo`/gate-refusal witness; `ReadsAt.of_frame` + `GetEnvFrame` give `ReadsAt` at the second world from the first | the reduction: yes, with `readMachine_gates` stated as a premise of its exact type (**A6c**); the premise itself: no (not importable) | **A6c below**: implemented, clean build `acv-d9a894b2` exit 0 (737 jobs), approved at d9a894b2 (conditional on `GetEnvFrame` / `ReaderRunsAt` / start `ReadsAt` as inputs; `hshape` to be discharged by `readMachine_gates` at an integration SHA) |
| G2 | existence of the `readMachine c false` run per reached `c` | DG-READKINDS / DG-COVER (real-run tie / coverage) | no supplier found | not supplied / no route found |
| G3 | `ReadsAt env₀` at the start world of that run | DG-ENV U2 (in progress), `readsAt_self` (E1) only for the start of the whole run | no supplier found for arbitrary reader start worlds | not supplied (owner dg-env) |
| C | `ClosesOfShape` | `closes_of_data` `[B]`, `dataOfFrom_sound` conj. 2,3 (`kjob/g5do-r6`) | existence of `d` (= `ReachCover` data part) and `CallsClose` supplier not found | not supplied / no route found |
| V | `ReachCover` | DG-COVER Cover3-6, DG-DATAOF row 6b | given a reader run / `dataOfFrom = some` only | not supplied / no route found (owners dg-cover, dg-dataof) |
| R | `ReadsSupplyAt` | DG-ENV U1 `[B]` / U2 | FG's non-strengthened `L`, `GetEnvFrame`: not supplied | not supplied (owner dg-env) |
| D | `DataOfShape K` | `dataOfAt_sound` conj. 1 (`kjob/g5do-r6`) | not importable here | integration obligation |
| E | `hcl` / reach closure | `ReachEdge.edge` `[B]` (supplied for `ReachEdge K Top`); reach U2/U5/U6/U7 | no new closing row found beyond `ReachEdge K Top` | supplied for `ReachEdge K Top`, else premise |
| O | `OffRouteServes`, `GenSFacts` | none found; DG-SEM | — | not supplied / no route found |

Rows C, V, R, D, E, O were re-read at the level of the rev5 table; this survey did not find a new closing step for them in the files read.

## 1. Chosen unit: A6c `gateRunsAt_of_readerRuns` (new file `Tools/ShippingGen5AccReader.lean`, imports `Tools.ShippingGen5AccGates`)

Reason: it is the only remaining row where the approved supplier's conclusion shape is fixed (`readMachine_gates`), the missing step is a small law-free transport that no other issue owns
(the linked witness `wE' = w1` and `ReadsAt` at `w1` come from the same run: `ReadsAt` at the start + `GetEnvFrame`), and it cuts the premises A6b leaves for integration from
"two `ReadsAt` worlds + an unlinked pair" to "one reader run + `ReadsAt` at its start world". It does NOT re-prove `readMachine_gates` (owner dg-readkinds) and supplies no run.

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEnvSnapshot (GetEnvFrame)

/-- The statement of `readMachine_gates` (dg-readkinds U8d), for one name, with `GenEntry ci env` written out as `entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)`. -/
def ReaderGateShape (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (c : Name) : Prop :=
  ∀ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
    RunsTo (readMachine c false) mctx mref cctx cref w r w' →
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
        (instancePredicate env) = none

/-- For every reached name found in `env₀`: one successful `readMachine c false` run whose start world satisfies `ReadsAt env₀`. -/
def ReaderRunsAt (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
      ReadsAt env₀ cref w ∧ RunsTo (readMachine c false) mctx mref cctx cref w r w'

theorem gateRunsAt_of_readerRuns {env₀ : Environment} (mctx : Meta.Context)
    (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (Reach : Name → Prop) (hg : GetEnvFrame mctx mref cctx cref)
    (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c)
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) : GateRunsAt env₀ mctx mref cctx cref Reach
```
Proof plan: for `c, ci₀`, take `w r w'` from `h`; `hshape` gives `ci env w1 w2`, both runs and both refusals; `ReadsAt env₀ cref w1` by `ReadsAt.of_frame hg he hw`; instantiate `GateRunsAt` with `wE := w`, `wE' := w1`.
Corollary (same file, one line): `gatesNoneAt_of_readerRuns` := `gatesNoneAt_of_gateRunsAt` applied to the above (same premises, conclusion `GatesNoneAt env₀ Reach`).
```lean
theorem gatesNoneAt_of_readerRuns {env₀ : Environment} (mctx : Meta.Context)
    (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (Reach : Name → Prop) (hg : GetEnvFrame mctx mref cctx cref)
    (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c)
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) : GatesNoneAt env₀ Reach
```
Premise status (not new laws): `GetEnvFrame` is the existing named premise of DG-ENV (already a premise of `readsSupply_of_quiet`); `hshape` is the statement of the approved theorem `readMachine_gates`, discharged at integration by `fun _ _ _ _ h => by unfold GenEntry …` (`GenEntry` unfolds to the written-out `entryConst`); `ReaderRunsAt` is the real-run tie, unsupplied. No change to `T1Hyp` / `T1HypND` / FG / shared definitions.
Not claimed: any reader run exists; `ReadsAt` at any start world; `readMachine_gates` re-proved; `ReachCover`, `ClosesOfShape`, `ReadsSupplyAt`, `DataOfShape`, off-route, `GenSFacts`; M5; FG. This lineage is before S1.

## 2. Check plan (`Tests/Gen5/AccReaderCheck.lean`, new)
TYPE: independent `Expected…` for the 2 definitions' bodies and the 2 theorems (written from §1 prose), `checkExpected` with `Tests.Gen3.ExpectedType`, positive control.
MUTANT (well-typed single change; signature/defeq rejection only): `ReaderGateShape` without the mixed conjunct; `ReaderRunsAt` without `ReadsAt`; `gateRunsAt_of_readerRuns` without `hg`; without `hshape`; `gatesNoneAt_of_readerRuns` without `h`. Counts reported as measured, with the rule.
CLOSURE: `closureReport` (unknown = fail, roots in `seen`, root / helper value / helper type unknown controls + clean, `withoutModifyingEnv`); AXIOMS standard three; no sorry in roots (isolated negatives counted and located).
Build one target at a time in the Pod; the Check is built on the committed tree; the Lean commit stays `doing` ("clean build is the coder's").

## 3. Not claimed
DG-ACC, M5, FG are not complete. EnvQ agreement stays a source-text comparison until the integration SHA. Not a supply of a reader run, `ReadsAt`, or any other row of §0.
