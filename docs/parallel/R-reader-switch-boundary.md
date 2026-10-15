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
| A solution of the source equation need not be reached by any fuel (so coverage does not follow from the equation alone) | `fixpoint_not_complete` | ReaderFuelGeneric | 0a53bd9e |

## Measured (not proved)
| Evidence | Scope | Commit |
|---|---|---|
| Driver vs real `machineShape?`: same class and all compared shape fields | 18 declarations (12 OUT→OK, 2 OUT→FAIL, 4 immediate FAIL) | 65eaccbb |
| prodMatcherArity?/projChain shadows (earlier switches) | grid + 260k-constant sweep | 9b86eb38 |

## Unmodelled / open (NOT axioms, NOT binders)
| Id | Statement | Why outside |
|---|---|---|
| O1 | A run of the compiled `partial` reader that RETURNS corresponds to a finite derivation (`Eval`), hence to some fuel | the compiled code's runtime is not modelled; `Eval ↔ ∃ fuel` is proved, the link from the compiled run to `Eval` is not |
| O2 | The real compiled `partial` constants satisfy their verbatim source equations (`OldEqV`) | properties of opaque compiled constants are not kernel-checkable |
| O3 | Opaque Expr primitives (`instantiate1`, `liftLooseBVars`, `Expr.eqv`, …) and still-partial helpers (`rootFloat`, `zetaAll`, `rawNode`, …) behave as their text; they terminate | fixed constants inside `step`; their termination is not claimed |
| — | A final OUT of the bounded driver says nothing about the real reader | `2^rounds · start` is finite; deeper finite executions exist (P2 correction a3a1d2d4) |

## Still to produce before a switch decision (ruling 2026-10-16)
* Driver eventual completion (`∃ rounds`, same answer) — worker G.
* Wrapper-level R5 from every successful `machineShapeF` result + one consumer reduced — worker H.
* Fixed-list shadow over ~25–40 real declarations with low start fuel, all-field equality, timings, separate
  TIMEOUT class — worker I.
* OldEqV source version recorded + drift check — worker G.
A switch would in addition need: the compiler path calling the driver WITHOUT mapping OUT to refusal / legacy
(an unbounded driver, or OUT reported as an error), and the existing suite + shadows + corpus comparison
(corpus rerun not approved yet).
