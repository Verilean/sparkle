# Lead units for M3/M4/M5 while M2 continues (plan, 2026-10-29)

- **Requested by:** the user via the review relay. "②階層帰納法・③全経路・④汎用供給はまだ開始できないか" was answered "開始可能".
- **Dependencies:** manager dependencies constrain only `done`, not starting work.
- **M2 keeps running.** S2-c, S4, then the S3/S5 freezes and StepStmt.
- **Unchanged:** FG/T1/M2 acceptance. Any guarantee or acceptance change is proposed BEFORE it is used.

## Units, order, dependencies
| order | issue | milestone | deliverable | depends on (for `done`) | may start |
|---|---|---|---|---|---|
| 1 (highest) | `sparkle-gen5-t2probe` | M5 | t2 route freeze + small kernel probe on a generic statement | D-GEN (`sparkle-gen5-dgen`) for the final `Generated`; the probe fixes only the fragment t2 needs | now |
| 2 | `sparkle-gen3-induct` | M3 | induction-step connection freeze over the A-COMB `ChildShips`; connection lemmas proved CONDITIONALLY on `StepStmt` (labelled) | M2 (`StepStmt`) for an unconditional result | now |
| 3 (light, parallel) | `sparkle-gen4-routes` | M4 | route census: every successful dispatch route, package ↔ consumer per route, the routes the current interface cannot express; freeze of the smallest independent route | M3 for use inside the induction | now |

## Why t2 first
G3GEN_CALL_PLAN.md §5 names t2 as the known risk: the call term's arguments are the let observations at `args`, and t2 may not be stateable from `body_eq` and the reader. t1 is the generator's own `machineExt` construction, and t3 is G3-DECL by construction. A failure of t2 would change how G-CALLDEC is supplied: a generator certificate, with cases (a)/(b)/(c). That is the late surprise to remove early.

The t2 unit must test GENERIC supply, i.e. the statement over every generated package. Adding another design's facts does not count.

## Isolation
- **Research:** each unit's research is read-only first, so it does not conflict with M2 edits on `par/gen2-spec`.
- **Lean probes:** these get their own worktree from a reviewed base. The base is 1fdbc18d (S6+S1, scoped-approved), or a later reviewed head. Their files are new and non-overlapping, and their builds are issue-linked, exact-head and focused.
- **Lake:** never two builds on one checkout or `.lake`.

## Not claimed
- Starting these units claims no progress of M2.
- A conditional connection lemma (on `StepStmt`) is not M3 progress toward `done` until `StepStmt` is proved.
