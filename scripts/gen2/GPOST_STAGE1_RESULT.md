# G-POST stage 1 (`InstClosed` in `ShipsRes`, `PostFactsStmt`, PF skeleton): re-verification result

- **Issue:** `sparkle-gen3-post`.
- **Freeze:** GPOST_FREEZE rev1 (fd893323) + §11 (33970372).
- **Branch:** `par/gen3-induct`.
- **Source:** 28476add.

## Build `g3pf-28476add` (head = base = 28476add)
- **Result:** exit 0, 973 jobs, log `def63a97bf32ef9d`, no `sorryAx`. No root outside `[propext, Classical.choice, Quot.sound]` or a subset.
- **NEW evidence, at the new `ShipsRes`.** Everything listed is newly Built:
  - `Tools.ShippingGen2{Defs, PostFacts, T1, KeepChild, Connect, Consumer, Keep, Data, CallDec, Adapt, AComb, C6, LoopRestrict, MemBd, MemData, MemFacts, MemKids, MemParent, MemShips, MemTop}`;
  - `Tests.Gen2.{U0Check, CallDecInstance, AdaptInstance, MemParentInstance, PkgCompat, QuantEndpoint, QuantInstance}`;
  - `Tests.Gen3.T1Check`.
- **Audited roots:**
  - `limitStmt_proved`, `servedShipsStmt_of_0`, `childShips_congr`, `ihAt_limit`;
  - `ihAt_stepPF`, `ih_allPF`, `t1_of_stepPF`, `t1_of_stepPF'`;
  - `shipsRes_old`, `invAt_old`, `servedP_old`, `stepStmt_of_old`;
  - `keepChild_proved`, `synthesizeChild_shipsRes`, `t1_of_stepPF_kc`.
- **OLD evidence** (pre-`InstClosed`) remains history:
  - `g3in-b6625408` / `g3in-ax-c6516331` (t1_of_step);
  - `g3kc-9b79bf3a` (keepChild_proved at the old `ShipsRes`).
- **Not in this branch's base,** so not re-verified here: `leaf_ships`, `slotlessLeaf_ships`, `Pkg.comb` (par/gen2-spec). They must be re-verified on integration.

## Status
- **`t1_of_stepPF`/`t1_of_stepPF_kc` are CONDITIONAL on `PostFactsStmt`** (plus `StepStmt` and `ServedShips0Stmt`).
- **Retired:** `NoTopStmt`, `ihAt_step`, `ih_all`, `t1_of_step(')` and `t1_of_step_kc`. They cannot supply the new conjunct.
- **PkgCompat:** the `Old → new` lifts of `ShipsRes`/`CacheShips`/`InvAt` take `InstClosed` as an explicit premise; `Old` does not give it.
- **Producer not written.** `postFacts_proved` will take `∀ q, DataOk q → DataRows q` (§11 wording; §5 differs).
- **Unsupplied:** P7, U1 (G-ONEOUT-REACH) and U2 (G-REACH).
