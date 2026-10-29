# M3 lead: the T1 induction-step connection — result (CONDITIONAL)

- **Issue:** `sparkle-gen3-induct`.
- **Freeze:** `par/gen2-spec` scripts/gen2/T1_CONNECT_FREEZE.md rev1, approved at eae85955.
- **Worktree / branch:** `~/git/.kjob/gen3-induct`, `par/gen3-induct`, from reviewed base 1fdbc18d.
- **Changes:** new files only (`Tools/ShippingGen2T1.lean`, `Tests/Gen3/T1Check.lean`, this doc) and their lakefile entries.

## Builds
| job | head = base | result |
|---|---|---|
| `g3in-b6625408` | b6625408 | exit 0, 704 jobs, log `e4e6a5ebc6fb5718`, `Tools.ShippingGen2T1` Built, no sorry |
| `g3in-ax-c6516331` | c6516331 | exit 0, 705 jobs, log `d95000c09f7447ce`, `Tests.Gen3.T1Check` Built, no sorryAx |

**Axioms.** `limitStmt_proved`, `servedShipsStmt_of_0`, `childShips_congr`, `ihAt_limit`, `ihAt_step`, `ih_all`, `t1_of_step` and `t1_of_step'` each depend only on `[propext, Classical.choice, Quot.sound]`.

## What is proved
- **`limitStmt_proved : LimitStmt L`** (kernel-checked JQ boundary). `JQ quiet D w` gives `dv w = D` (ChildVCA:53). At `sparkleSynthDepthLimit ≤ D` the core run throws: `core_limit_triple`, the limit prefix of `core_tripleAC`, with the invariant `JQ`.
- **`servedShipsStmt_of_0 : ServedShips0Stmt … → ServedShipsStmt …`.** This is the implication only. No strictness is claimed.
- **`childShips_congr`, `ihAt_limit`, `ihAt_step`, and `ih_all`** (`T1Hyp` explicit).
- **`t1_of_step`, CONDITIONAL**, with the frozen §3 type: `StepStmt → KeepChildStmt → ServedShips0Stmt → NoTopStmt → LimitStmt → T1Stmt`.
- **`t1_of_step'`:** the same with `LimitStmt` discharged.

## Status of the premises (unchanged; NOT proved here)
| premise | gap / unit |
|---|---|
| `StepStmt` | M2-b (`sparkle-gen2-step`) |
| `KeepChildStmt` | G-KEEP-CHILD / G-EXC |
| `ServedShips0Stmt` | G-SERVED + G-START (includes G-ONEOUT-REACH) |
| `NoTopStmt` | G-POST |

## Notes
- **Where `NoTopStmt` is used:** only in `ihAt_step`, to move `ChildShips` to the full design. The top case of `t1_of_step` does not need it, because `T1Stmt` speaks about the core design.
- **G-MEMO:** recorded as a dispatch exclusion under `T1Hyp.defines`/`closes`. This is NOT a cache invariant.
- **The route-indexed `T1Hyp`** (ROUTE_CENSUS rev2) is not applied. The skeleton covers machine-route trees under the current `T1Hyp`.
- **Not claimed:** M2, M3 or FG completion. The result is conditional.
