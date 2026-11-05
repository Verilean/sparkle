# G-POST assembly note (issue `sparkle-gen3-post`)

- **Base:** `par/gen3-induct` 35588c38. Freeze: GPOST_FREEZE rev1 + §11; F1 from SERVED_FREEZE rev1 (accepted b5be62e6).
- **Status:** committed 23896e06, fixed a9c42458 (implicit tenv); built clean in g3pf3-a9c42458 (716 jobs, TYPE 4, MUTANT 5,
  AXIOMS 9); approved as a CONDITIONAL producer (hrows, hrow). U2 supplied locally, not G-REACH coverage.

## Files (new only; no existing `.lean` edited)
- `Tools/ShippingGen2PostFactsProof.lean`: the producer. `Tools/ShippingGen2PostFacts.lean` already holds the
  statements (built at 28476add), so the producer goes in a new file and that file is not edited.
- `Tests/Gen3/PostFactsCheck.lean`: expected types, mutants, terms and axioms.
- `Tests/Gen3/PostExpectedType.lean`: a namespaced copy of `Tests/Gen3/ServedExpectedType.lean`.
- lakefile entries (added at 23896e06):
  - `Tools.ShippingGen2PostFactsProof`
  - `Tests.Gen3.PostExpectedType`
  - `Tests.Gen3.PostFactsCheck`

## Results (all CONDITIONAL)
| name | statement |
|---|---|
| `postFacts_proved` | `(hrows) (hrow) → PostFactsStmt L P Reach DataOk` |
| `postFacts_of_hord` | the same, with the semantic `hord` in place of `hrow` |
| `t1_of_step_rows` | `(hrows) (hrow) (hStep : StepStmt) → T1Stmt` (`t1_of_stepPF_served` + the producer) |

## Supplied inside the proof
- **P1:** `machineRunInv_of_coreA` (F1, imported) plus `T1Hyp.closes`, which gives `r = some`.
- **P2:** `synthesizeMachineCertified_runsS` (F1). It also supplies P7's `hlen`, from the `ChildrenShipsI` length
  conjunct.
- **P3:** `closedBody_kinds_of_run`, which gives `d₀.modules = []` under `DataRows`.
- **P4/P6:** `closeInsts(G)_design` and `closeInsts(G)_acyclic`. P6 is used at `raw.name` directly, so P4's name
  equation is not needed.
- **P5:** `closeInsts_names` + `closeInsts_acyclic`, and `closeInstsG_names`.
- **P7:** `closeInsts(G)_kids_inst`.
- **P8:** `mem_designWith` + `mem_visited`.
- **P9:** `instOrigin_child?_mem` and the memory module's design `[md.1]` (by `rfl`).
- **P10:** `inst_target_full`.
- **Memory children:**
  - general closing: `MemChildren`;
  - one-output closing: a memory origin is excluded by `hord`.
- **Ordinary children:** `T1Hyp.closed` gives `Reach`, then `ChildrenShipsI` gives `ShipsRes`, which gives
  `InstClosed`.

## Explicit premises that remain (UNSUPPLIED)
- **`hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q`** (§11 S1). It is used only for P3. `DataOkB` is unchanged.
- **`hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2ServedDataBridgeCopy.OneOutNoMemRow q = true`** (U1,
  G-ONEOUT-REACH).
  - It is the same R-ROW premise as `servedShips0_proved`, used through the local copy `hord_of_row`.
  - It is needed only for the one-output closing.
  - Supplying it is `sparkle-gen3-data-supply`. A census or a single instance is not supply.

## Not premises
- **U2 (G-REACH).** Every module of the core design comes from the closing's `children`, which are indexed by
  `q.d.shape.insts`. `T1Hyp.closed` on that shape gives the reach directly. The translator's own calls add no module,
  because `d₀.modules = []` by P3.
- **Not used:** `MachineTaken`, the full-entry run and `htop`. They stay as binders of the frozen statement.

## Not claimed
- G-POST, T1/M3 or FG completion while `hrows`/`hrow` are unsupplied.
- The build.
- The `.comb` constructor: the producer is written against this base's 2-constructor `Pkg` and uses no `cases`
  on `Pkg`, but it must be re-elaborated at integration.
