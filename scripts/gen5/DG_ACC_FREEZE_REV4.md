# DG-ACC freeze rev4 (issue `sparkle-gen5-dg-acc`): supply survey for the premises of `AccServed0Stmt`, and the first unit A6a

**FOR REVIEW (docs only; no Lean for A6a is written until this is approved).** Rev1-rev3 are unchanged. Base: `kjob/g5ac-r7` (A5a/A5b approved at a88c3e9c; clean build `ac6v-a88c3e9c`,
exit 0, 724 jobs; headers and rev3 §7 synced at 8d4f7c88, comment/docs only).

Tags: `[S]` source read (this worktree, or the named branch via `git show`/`git grep`); `[B]` built (named build); `[E]` the text below elaborates in a Pod scratch file
(`kjob lake env lean`, scratchpad, **not committed**; here the statements AND a proof attempt of A6a elaborated, exit 0, standard axioms `propext, Classical.choice, Quot.sound`;
the proof is not part of this freeze and is not counted as an implementation).
Wording: "not supplied / no route found" means *this survey did not find a supplier or route in the files read*; it never says "impossible" or "underivable".
A MUTANT is a rejection of a changed, well-typed statement by signature / defeq, **not** a semantic counterexample. Conditional results are INTERMEDIATE, never completion.
The branches read are: `kjob/g5cv-r13` (DG-COVER, Cover2-6), `kjob/g5do-r6` (DG-DATAOF), `kjob/g5sm-u7` (DG-SEM), `kjob/g5rk-r14` (DG-READKINDS U5-U8), `kjob/g5env-r6`
(DG-ENV / CLOSINGRUN), `par/gen2-spec` `scripts/gen2/ROUTE_CENSUS.md`. None of them is an ancestor of this lineage (see §4 for what that means for the next unit).

## 0. Summary

| premise of `accServed0_of_cover` | result of this survey |
|---|---|
| `hcl : ∀ X c, Reach X → CallEdge K X c → Reach c` | **Supplied** for `Reach := ReachEdge K Top` (constructor `ReachEdge.edge`, `Tools/ShippingGen5Acc.lean:201-203`, `[B]`). For an arbitrary `Reach` it is a hypothesis on that `Reach`. |
| `DataOfShape K` | **Supplied at integration, not in this lineage**: it is conjunct 1 of `Tools.ShippingGen5DataOf.dataOfAt_sound` (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:211`, `[S]`; file clean-built `do5v-945fbe9a` per its header) once the kit field `K.dataOf` is instantiated by `dataOfAt lvl` (A6). No step for it can be written here (DataOf is not imported by this lineage). |
| `ReachCover K Reach` | **Not supplied / no route found.** It needs `entry₀ env₀ c = some E` and `K.genData₀ E = some g` for every reached `c`; `genData₀` exists only if `dataOfAt … = some _` and `GenWF` hold. DG-DATAOF §11.2 lists rows 1-6, 8 of "`dataOfFrom … = some`" as open (`kjob/g5do-r6:scripts/gen5/DG_DATAOF_FREEZE.md` §11.2); DG-COVER's closed pieces (§2) are reader-state invariants, not this existence. Owners: dg-dataof, dg-readertrace, dg-cover, dg-readkinds (named in §2). |
| `MachineRouteAt env₀ L Reach` | **Split into three rows by A6a** (§3): shape existence and the `env₀`-side `machineShape?` equation are **derivable from `ReachCover` + the kit field `genData₀_dataOf`** (new unit A6a, §1); what remains is `GatesNoneAt` (the two gate refusals at `env₀`) and `ClosesOfShape` (`MachineClosesAtA`). Both remain **not supplied / no route found** (§2 rows R3, R4). |
| `ReadsSupplyAt env₀ L Reach` | Built for the quiet-strengthened `L'` from `QuietStrengthA` + `GetEnvFrame` (rev2 §B); `QuietStrengthA`/`AdmDownA` are string-checked copies of EnvQ's; `GetEnvFrame` and the non-strengthened `L` are not supplied (§2 row R5). DG-ENV owns it (U1 approved at a14f2479, U2 in progress). |
| `OffRouteServes` | Not supplied; no issue found that owns it (§2 row R6). |
| `GenSFacts` (A3, not used by A5) | Partly: DG-SEM supplies `GenExtAtCall` and the memory facts for `genSemI`; the assembled `FactsOf (.gen _)` (incl. `causal`) is not supplied (§2 row R7). Owner: dg-sem. |

First unit to implement (after approval): **A6a `machineRouteAt_of_cover`** (§1). Reason: it is the only row of this survey that is both (a) closable from parts that are already in this lineage's
base (`machineDefinesR_of_env` in `Tools/ShippingGen5EnvR.lean`, the kit field `genData₀_dataOf`, `ReachCover`, `accServed0_of_cover`; no import of a not-yet-integrated branch) and
(b) not owned by another issue. It replaces the premise `MachineRouteAt` (shape existence + `MachineDefinesR` + `MachineClosesAtA`) by two narrower, separately attributable rows.
It does **not** supply `ReachCover`, the gates or the closes row, and it does not close `AccServed0Stmt` unconditionally.

No new law, no TRUSTED boundary, no FG change, no change to `T1Hyp`/`T1HypND`, no shared or compiler file. All new Lean goes into new files (§4).

## 1. A6a: complete types `[E]` (file `Tools/ShippingGen5AccRoute.lean`; imports `Tools.ShippingGen5AccServed`)

Preamble, as in `Tools/ShippingGen5AccServed.lean` (the names `MachineRouteAt`, `ReachCover`, `DataOfShape`, `ReadsSupplyAt`, `accServed0_of_cover`, `AdmCtx`, `MachineClosesAtA`, `MachineDefinesR` are those of A1-A5):
```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)
open Sparkle.IR.Machine

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

/-- The two gate refusals of `MachineDefines`, at `env₀`, for the entry constant of every reached name. -/
def GatesNoneAt (env₀ : Environment) (Reach : Name → Prop) : Prop :=
  ∀ c ci, Reach c → env₀.find? c = some ci →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none

/-- `MachineClosesAtA` for the machine shape of the entry constant of every reached name. -/
def ClosesOfShape (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c ci shape, Reach c → env₀.find? c = some ci →
    machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c shape

theorem machineRouteAt_of_cover (L : Laws mref cref) (Reach : Name → Prop)
    (hcov : ReachCover K Reach) (hG : GatesNoneAt env₀ Reach) (hC : ClosesOfShape env₀ L Reach) :
    MachineRouteAt env₀ L Reach

theorem accServed0_of_cover_gates (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hcov : ReachCover K Reach) (hDS : DataOfShape K) (hG : GatesNoneAt env₀ Reach)
    (hC : ClosesOfShape env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach
```
(Both theorem bodies are `by …` / a one-line application in the implementation; the freeze fixes the statements and the two definition bodies only.)

Proof route (planned, `[E]` in scratch): from `hcov c hc` get `E`, `g`, `entry₀ env₀ c = some E`, `K.genData₀ E = some g`; unfolding `entry₀` gives `env₀.find? c = some ci` and
`E = entryConst … ci …`; `K.genData₀_dataOf hg : (machineShape? false [] E (structEnv env₀)).bind (K.dataOf E (structEnv env₀)) = some (K.dOf g)` forces `machineShape? … = some shape`
(an `Option.bind` that is `some` has a `some` head); then `machineDefinesR_of_env` (`Tools/ShippingGen5EnvR.lean:50`, `[B]`) with `hG` gives `MachineDefinesR`, and `hC` gives `MachineClosesAtA`.
`accServed0_of_cover_gates` is `accServed0_of_cover` applied to `machineRouteAt_of_cover …`.

What A6a does and does not claim:
* It supplies, **given `ReachCover`**, the shape existence and the `env₀`-side `find?`/`machineShape?` facts that `machineDefinesR_of_env` needs. It is a re-attribution of `MachineRouteAt`, not a supply of the gates or of `MachineClosesAtA`.
* `GatesNoneAt` is the gate-refusal conjunct of `T1Hyp.defines`' `MachineDefines` (`ROUTE_CENSUS.md` §2: routes 1/2 are "not expressible" by `T1Hyp.defines`; "FG is not narrowed by this; the coverage obligation is M4"). A6a does **not** restrict `Reach` to route-3 names and does not narrow the FG.
* Single-change MUTANT plan (signature/defeq rejection, not semantic): `machineRouteAt_of_cover` without `hG`; without `hC`; without `hcov`; `GatesNoneAt` with the `mixedCertifiedShape?` conjunct dropped; `ClosesOfShape` with `AdmCtx` premise dropped; `accServed0_of_cover_gates` without `hDS`; a mutant dropping the `hRS` premise. Counts will be reported as measured with their classification rule.

## 2. Supplier table (real names; "owner" = the issue whose branch holds or is to hold the supply; this issue does not re-implement their rows)

| row | what is needed | existing parts read (`[S]` unless `[B]`) | state |
|---|---|---|---|
| R1 `hcl` | closure of `Reach` under static ordinary edges | `ReachEdge.edge` (`Tools/ShippingGen5Acc.lean:201-203`, `[B]`) for `Reach := ReachEdge K Top` | **supplied** for that `Reach` |
| R2a `ReachCover` (entry part) | `entry₀ env₀ c = some E` for reached `c` | `entry₀` is `(env₀.find? c).map (entryConst …)`; `find?` for every reached name is a census fact: DG-COVER/ENV census content (DG-ENV class rows). | **not supplied / no route found** (owner: dg-env, dg-cover) |
| R2b `ReachCover` (data part) | `K.genData₀ E = some g`, i.e. `dataOfAt lvl E senv shape = some d` plus `GenWF` | DG-DATAOF §11.2 rows 1,2,3,4,5,6,8 open; 7 depends on 4,5 (`kjob/g5do-r6:scripts/gen5/DG_DATAOF_FREEZE.md` §11.2). Closed pieces: row 6b projections `dataOfFrom_dims`/`dataOfAt_dims` (`kjob/g5do-r6:Tools/ShippingGen5DataOfDims.lean:108`; agent build only). DG-COVER closed pieces: `shapeAgree_of_production`, `shapeAgree_of_sides` (`kjob/g5cv-r13:Tools/ShippingGen5Cover5.lean:76,97`), `rowC_of_reader_ok` (`Cover4`), `rowA2/3/B1_of_inv` (`Cover3`), `fullInv_reachC`, `reserved_reachC` (`Cover6`): they give `ShapeAgree` rows from reader-state invariants **of a given reader run**, not existence of the run. READKINDS U5-U8 (`kjob/g5rk-r14`): `RootFacts`, `readMachine_root`, `readMachine_fields`, `machineDefines_of_readsAll`-based statements, all about a given `readMachine` run (`hall` premise, design-only for U8). C-QWIT/C-CMP/S-OK/S-COV-FLOAT: no run supplier found. | **not supplied / no route found** (owners: dg-dataof, dg-readertrace, dg-readkinds, dg-cover, dg-wfcover) |
| R2c `DataOfShape K` | `K.dataOf E se s = some d → d.shape = s` | `dataOfAt_sound` conj. 1 (`kjob/g5do-r6:Tools/ShippingGen5DataOf.lean:211`) with `K.dataOf := dataOfAt lvl` | **supplied at integration (A6)**; not importable on this lineage |
| R3 `GatesNoneAt env₀ Reach` | both gate refusals at `env₀` for the entry constant of every reached name | `machineDefinesR_of_env` takes them as `hg1 hg2` (`Tools/ShippingGen5EnvR.lean:50`). `ROUTE_CENSUS.md` §1-§2: routes 1/2 are first/mixed gate successes; the census says a reached name taking a gate is outside `T1Hyp.defines` and calls this "the coverage obligation is M4". DG-COVER's DataOf rows contain no gate statement (`S-COV-GATE` is "not a `dataOf` obligation", DG-DATAOF §4). | **not supplied / no route found** (owner not identified; this is the route-3-membership question of M4, not decided here) |
| R4 `ClosesOfShape` | `MachineClosesAtA` for the route shape | `closes_of_data` (`Tools/ShippingMachineClosesData.lean:226`; no calls, needs `d.ok`, the body equation, `d.letsOk`) then `machineClosesAtA_of_closes` (A5b, `[B]`): `d.ok` and body equation are `dataOf_sound` conj. 2,3 for a `d` that exists (R2b), so the no-call case is **conditional on R2b and on `d.letsOk = true`**; with calls: `closes_of_data_calls` needs `CallsClose` (`Tools/ShippingClosesSplit.lean:40`) and `memCallee_closesA` (`Tools/ShippingSrm3Callee.lean:91`) needs `MemCalleeData`/`hord`; no supplier of `CallsClose` found | **not supplied / no route found** (the no-call sub-case is a candidate next unit, conditional on R2b; not started) |
| R5 `ReadsSupplyAt env₀ L Reach` | `ReadsAt env₀` at the run's chain worlds | rev2 §B (`Tools/ShippingGen5AccReads.lean`, `[B]`): holds for the strengthened `L'` from `QuietStrengthA` + `GetEnvFrame`. DG-ENV: EnvQ `QuietStrength`/`AdmDown` (originals), `EnvFrame` (`kjob/g5env-r6:Tools/ShippingGen5EnvFrame.lean`), `ClosingRun`/`ClosingRun2` (`kjob/g5env-r6`). | **not supplied** for the FG's `L`; the originals are not importable on this base (T2Tie does not elaborate before S1). Owner: dg-env |
| R6 `OffRouteServes` | reached names off route 3 (gate route 1/2, or legacy after a refused machine synthesis, `ROUTE_CENSUS.md` routes 4-6) | none found; `MachineRouteAt` excludes such names by hypothesis, it does not serve them | **not supplied / no route found**; no owner found among the issues read. (A decision about route-3 membership of `Reach` belongs with R3.) |
| R7 `GenSFacts` | `∀ X s, genS K X = some s → FactsOf s` | DG-SEM (`kjob/g5sm-u7`): `genExtAtCall_of_genSem` (`Tools/ShippingGen5SemExtPkg.lean:17`, conditional on `hp hq hord`; its Pod build needs a one-line local fix of `T2Tie.callField_at`), `memFacts_of_genSem` (`Tools/ShippingGen5SemMem.lean:108`), `genSemI_local/_decl/_d`; DG-SEM freeze rev3 plans `genFacts_gen`, `genSemGen_facts` (P6' `causal`): not in the tree | **not supplied** (owner: dg-sem) |
| R8 `AccKeepChildStmt` | | A5a, `[B]` | **closed** (no premise) |

## 3. How the premise `MachineRouteAt` decomposes after A6a (for the reader)

`MachineRouteAt env₀ L Reach` = for each reached `c`: `∃ shape, MachineDefinesR … ∧ MachineClosesAtA …`.
After A6a: shape existence + `find?`/`machineShape?` facts ⇐ `ReachCover` (R2) + kit field; `MachineDefinesR` ⇐ those + `GatesNoneAt` (R3); `MachineClosesAtA` ⇐ `ClosesOfShape` (R4).
So the cover form of `AccServed0Stmt` is conditional on {R1 (supplied for `ReachEdge`), R2 (a), (b), R2c (integration), R3, R4, R5}; R6 and R7 are outside this form (R6 excluded by hypothesis, R7 not used by A5).

## 4. Constraints of this lineage, and obligations at integration

* The lineage is before S1: `Tools/ShippingGen5T2Tie.lean` does not elaborate at this base, so `Tools/ShippingGen5EnvQ.lean` and everything importing it (also `kjob/g5do-r6`'s `DataOf*`, `kjob/g5sm-u7`'s `SemExtPkg`, which import T2 files) cannot be imported. A6a imports only `Tools.ShippingGen5AccServed`.
* **EnvQ agreement is a text comparison, not a typed one.** `QuietStrengthA`/`AdmDownA` (`Tools/ShippingGen5AccReads.lean`) are compared as source text by `AccServedCheck` with a positive and a negative control. That is *not* counted as a typed match. **Obligation at the integration SHA** (where EnvQ is importable): replace the copies by EnvQ's originals or prove them `defeq`/equal to the originals in a typed check, and re-run `AccServedCheck`/`AccReadsCheck`. The same applies to any further text copied from another branch.
* `DataOfShape K` (R2c) and the instantiation `K.dataOf := dataOfAt lvl` are also integration obligations (A6); no Lean in this lineage depends on them.

## 5. Implementation plan after approval (new files; no built, shared or compiler file changed; lakefile `lean_lib` entries)

| file | contents |
|---|---|
| `Tools/ShippingGen5AccRoute.lean` (A6a) | §1: `GatesNoneAt`, `ClosesOfShape`, `machineRouteAt_of_cover`, `accServed0_of_cover_gates` |
| `Tests/Gen5/AccRouteCheck.lean` | TYPE (independent `Expected…` statements written from this freeze, `checkExpected` binder by binder, every definition and theorem), DEFBODY for the two definitions, MUTANT (the plan in §1, well-typed single-change statements only, plus a conjunct-drop mutant for `GatesNoneAt`), AXIOMS (standard three), CLOSURE via `closureReport` (unknown name = failure; root itself in `seen`; unknown-name controls for root, helper value and the type of an existing helper, plus the clean control; `withoutModifyingEnv`), `sorry` absent from proof roots (any isolated negative fixture counted and located) |

Build: `kjob lake build` one target at a time; the Lean commit is left in `doing` ("clean build is the coder's").

## 6. Not claimed
DG-ACC is **not** done. A6a, once implemented, is a re-attribution of `MachineRouteAt` into narrower named premises plus the derivation of shape existence from `ReachCover`; it does not supply `ReachCover`, `GatesNoneAt`,
`ClosesOfShape`, `ReadsSupplyAt` for the FG's `L`, `OffRouteServes`, `GenSFacts`, or the EnvQ typed agreement. No claim about M5 or the FG; no change to FG, `T1Hyp`/`T1HypND`, a law, a TRUSTED boundary, the compiler or `GenWF`.
