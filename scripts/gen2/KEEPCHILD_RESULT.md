# M3: G-KEEP-CHILD / G-EXC — result

- **Issue:** `sparkle-gen3-keepchild`.
- **Freeze:** KEEPCHILD_POST_FREEZE.md §B, approved at f7fb323c.
- **Branch:** `par/gen3-induct`.
- **Changes:** one new file, `Tools/ShippingGen2KeepChild.lean`, and its lakefile entry. No Defs change.

## Build
- **`g3kc-9b79bf3a`** at 9b79bf3a (= base_head): exit 0, 705 jobs, log SHA-256 prefix `709ecfcda418b22e`, no `sorryAx`.
- **Axioms:** `keepChild_proved`, `synthesizeChild_shipsRes` and `t1_of_step_kc` depend only on `[propext, Classical.choice, Quot.sound]`.

## What is proved
- **`keepChild_proved : KeepChildStmt L P Reach`,** on the CURRENT `ShipsRes`/`InvAt`. This is the all-outcome keep of the child entry at `InvAt`, throwing runs included. It uses lemmas #1-#13: copies of the `ChildPinC` chain with `JQP` replaced by `InvAt`, plus `cacheShips_insert` and `invAt_insert_runs`.
- **#13 `synthesizeChild_shipsRes`** (no `hentryT`). It decomposes the returning run: cache read, then hit or miss.
  - **Hit:** `CacheShips` of the post-read world.
  - **Miss:** `IHAt` at the PRE-ENTRY world `w1`, the world after the framed cache read, which satisfies `InvAt D` and is the start of the inner full-entry run.
  - **Deviation from the freeze row:** it also takes `hA : AdmCtx L.O.quiet mctx cctx`, the admissible-context premise that `IHAt` and the framed read need. It is not a new fact.
- **`t1_of_step_kc`:** `t1_of_step` with `KeepChildStmt` discharged. It remains CONDITIONAL on `StepStmt`, `ServedShips0Stmt`, `NoTopStmt` (and `LimitStmt`, already proved).

## Not claimed
- G-SERVED, G-POST, M2 or M3 completion.
- **Status if `ShipsRes` gains `InstClosed`** (GPOST_COMPARE option B, under review): the proof is generic in `ShipsRes`, so `cacheShips_insert`/`invAt_insert_runs` carry over. A rebuild would be required.
