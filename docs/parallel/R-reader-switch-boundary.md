# Reader fuel candidate — boundary table (decision material for a production switch)

Integrator, 2026-10-16, poc a3a1d2d4. Ruling 2026-10-16 item 4: O1 / O2 are NOT added as axioms or allowed
binders. This table separates what is PROVED (kernel, standard axioms) about the isolated fuel candidate from
what is UNMODELLED about the old compiled `partial` reader. Production still calls the partial reader; nothing
here switches it.

## Proved (kernel)
| Claim | Theorem(s) | File | Commit |
|---|---|---|---|
| A finished fuel answer is stable under more fuel; two finished answers are equal | `fuel_stable`, `fuel_det`, `readF_stable`, `readF_det`, `machNormF_*` | ShippingReaderFuelKleene | 22908c5f |
| Finite-execution adequacy: `Eval senv c r ↔ ∃ n, readF senv n c = some r` (success and ordinary refusal; machNorm too) | `eval_fuel`, `fuel_eval`, `eval_iff`, `evalN_*` | ShippingReaderFuelEval | 36d6b5ef |
| Agreement with every solution of the transcribed old equations | `readF_agree_old`, `machNormF_agree_old` | ShippingReaderFuelOldEq | fc697219 |
| Agreement with every solution of the VERBATIM source equations of Elab.lean | `readF_agree_verbatim`, `machNormF_agree_verbatim` | ShippingReaderFuelVerbatim | 8fac0511 |
| R5 (LenOk) for every fuel and every successful result of the 7 fuel functions | `readersKeepLenOkF`, `machXF_lenOk` | ShippingReaderFuelR5 | 9a5ccc93 |
| Wrapper keeps OUT/FAIL/OK; OUT propagates through sharing probes | `findSomeO_out_append`, `findSomeO_fail_all`, `nestedStep_out_of_search` | ShippingReaderFuelShape | 65eaccbb |
| Bounded driver: FAIL / OK it returns are genuine and stable; it never produces FAIL for OUT | `driveShape_res`, `driveShape_fail_sound`, `driveShape_ok_sound` | ShippingReaderFuelDriver | 65eaccbb |
| Driver eventual completion: some fuel decides → some rounds give the same answer; OUT forever ↔ every fuel OUT; a finite wrapper derivation → driver answer | `driveShape_complete(_ok/_fail/_iff)`, `driveShape_out_forever_iff`, `shapeRuns_drive` | ShippingReaderFuelDriverComplete | fe65d4c5 |
| A solution of the source equation need not be reached by any fuel (so coverage does not follow from the equation alone) | `fixpoint_not_complete` | ReaderFuelGeneric | 0a53bd9e |

## Measured (not proved)
| Evidence | Scope | Commit |
|---|---|---|
| Driver vs real `machineShape?`: same class and all compared shape fields | 18 declarations (12 OUT→OK, 2 OUT→FAIL, 4 immediate FAIL) | 65eaccbb |
| prodMatcherArity?/projChain shadows (earlier switches) | grid + 260k-constant sweep | 9b86eb38 |
| Fixed-list shadow, start fuel 1: real vs driver, ALL shape fields | 40 real declarations (33 OUT→OK, 3 OUT→FAIL, 4 FAIL at 1), no TIMEOUT | f5df0683 |

## Unmodelled / open (NOT axioms, NOT binders)
| Id | Statement | Why outside |
|---|---|---|
| O1 | A run of the compiled `partial` reader that RETURNS corresponds to a finite derivation (`Eval`), hence to some fuel | the compiled code's runtime is not modelled; `Eval ↔ ∃ fuel` is proved, the link from the compiled run to `Eval` is not |
| O2 | The real compiled `partial` constants satisfy their verbatim source equations (`OldEqV`) | properties of opaque compiled constants are not kernel-checkable |
| O3 | Opaque Expr primitives (`instantiate1`, `liftLooseBVars`, `Expr.eqv`, …) and still-partial helpers (`rootFloat`, `zetaAll`, `rawNode`, …) behave as their text; they terminate | fixed constants inside `step`; their termination is not claimed |
| — | A final OUT of the bounded driver says nothing about the real reader | `2^rounds · start` is finite; deeper finite executions exist (P2 correction a3a1d2d4) |

## Still to produce before a switch decision (ruling 2026-10-16)
* Driver eventual completion — DONE (fe65d4c5).
* Wrapper-level R5 — DONE (see the section below).
* Fixed-list shadow — DONE (f5df0683): 40/40 equal.
* OldEqV source version recorded + drift check — DONE (fe65d4c5; `oldeqv_drift.py`, no drift).
A switch would in addition need: the compiler path calling the driver WITHOUT mapping OUT to refusal / legacy,
and the existing suite + shadows + corpus comparison (corpus rerun not approved yet).
CORRECTION (2026-10-17, reviewer): "OUT reported as an error" is NOT an acceptance-preserving route — a finite
budget followed by an error can reject an input the old reader accepted. Budget / cancellation errors may exist
only as experimental operational outcomes; they are neither a semantic refusal nor evidence of equivalence. The
only candidate route under consideration is an unbounded or resumable driver (no finite budget ending in a
verdict), and no production switch is planned.

## Wrapper-level R5 (worker H, 9eb01c91) — BUILT with integrator fixes
Applied on poc fbb445d0. Run `h1` (cgrun, 3 GiB, swap 0, `-j 1`). As written `Tools.ShippingReaderFuelShapeR5`
failed in two proofs (no statement changed): `okO_run_inv` (`injection` already closed the goal → one-line
`Option.some.inj`), `shapePost_decomp` (the inversion loop lacked `split at h` for the `match p.tup?` of the
output fields, and the final `ite` inversion is optional in some branches). Then `Tools.ShippingReaderFuelShapeR5`
and `Tools.ShippingCallWidthsEntryF` exit 0. Axioms of all theorems below: [propext, Classical.choice,
Quot.sound].
PROVED for EVERY successful candidate-wrapper result `machineShapeF n … = some (some sp)` (state kept through
start / root lets / body; `machineShapeF_steps`, `machineShapeF_lenOk`): `machineShapeF_decomp` (a `ShapeDecomp`
with names / kinds / inits of equal length), `machineShapeF_r5` (R5: `(names.zip kinds).length =
sp.layout.slots.length`), `machineShapeF_binderCount`, `machineShapeF_nDecl` (the closing's nDecl = `bs.length`),
`machineShapeF_callBinder`, `machineShapeF_slots_length`.
CONSUMER REDUCED (alternative next to the unchanged `entryStrict_of_links`): `entryStrict_of_linksF` /
`callWidthsStrict_of_linksF` — premises `NIN` (`d.nIn = bs.length + insts.length`) and `R5ok` (`d.r5Ok = true`)
DISAPPEAR, the links being candidate-wrapper successes (`LinkPF`, `LinkCF`).
NOT counted for the old compiler: these are about `machineShapeF`; transferring them to the real `machineShape?`
needs O1 + O2.
