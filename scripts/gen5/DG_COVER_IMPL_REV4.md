# DG-COVER rev4 implementation notes (Issue sparkle-gen5-dg-cover, branch kjob/g5cv-r6)

Implements the scoped-approved freeze `DG_COVER_FREEZE_REV4.md` (U-D1, U-D2, U-D3) in `Tools/ShippingGen5Cover3.lean` and `Tests/Gen5/Cover3Check.lean`
(+ two `lean_lib` entries). Lean commit `302525c0`; built in the Pod (`kjob lake build Tools.ShippingGen5Cover3`, then `Tests.Gen5.Cover3Check`, exit 0). Header-only
commit `9c7b5c35` records that SHA. **Clean exact-head build is the coder's; not done here.** No compiler / shared-definition / law / TRUSTED / FG change; `GenWF` not strengthened.

## Delivered (conditional theorems; INTERMEDIATE, not a completion of the Issue)
- U-D1: `readsOfQuoteStmt : ReadsOfQuoteStmt` (the rev2 statement, with `PhInRange`), via `looseOcc_machClose` and `reads_of_quote_loose`. Every constructor of `Term`,
  including `appCompare`/`appBool`/`appBool2` (through `appE`), `mux` (three operands) and the width helpers, has an operand-occurrence lemma `lo_*` (operand is an
  application argument at binder depth 0); `boolLit`/`bitsLit`/`bitsNum` read nothing. No helper stop condition was hit (no operand under a binder / `letE` / `proj` / `mdata`).
- U-D2: `InRange`, `RangeInv`, `OrigAligned`, `EntryKinds`, `FullInv`, `FStep` (letv/inst/group/slot/slots/ws), `FReach`; `fullInv_of_empty`, `fullInv_step`, `fullInv_reach`,
  `reach_sizes_mono`, `callOrderInv_group`; suppliers `letRange_final`, `writeRange_final`, `resultRange_final`, `machNext_range`, `machBundleParts_range`, `machResults_range`.
  The `group` arm carries the same `js` into every added entry (`group_get`), with `rs.length = os.length`.
- U-D3: `ShapeAgree`, `LetQuoteEq`, `LetsNoLoose` (premises, unsupplied), `cleanLets_getElem`, `letReach_edge`, `rowA2_of_inv`, `rowA3_of_inv`, `rowA4B23_mem_of_inv`,
  `rowB1_of_inv`, `rowC_of_reader` (strong induction on the let index over `LetReach`; `MentionPos` cases: input, instance via `ArgsInstBounded`, slot, let via `LetEdge`).

## Differences from the freeze text (reported, no semantic change)
1. `rowA2_of_inv` has no `{nDecl : Nat}` binder: the freeze text declares it but it occurs nowhere in the statement, so a use site could not infer it. All other
   theorem types are the freeze types (binder names / order checked by `Cover3Check`).
2. `looseOcc_machClose` is stated in the freeze binder order `d v b`; the proof is `looseOcc_machClose_aux` (order `v d b`) wrapped.
3. The freeze planned to compare `readsOfQuoteStmt` with `Tests.Gen5.CoverNegCheck.ReadsOfQuoteStmt` by defeq. The comparer rejected it (separately defined recursive
   `LooseOcc`/`MentionsPh` are not `isDefEq` on a variable argument). Instead: `Cover3Check` compares with a spelled-out `ExpReadsOfQuoteStmt`, and proves
   `mentionsPh_iff`, `looseOcc_iff`, `negcheck_readsOfQuoteStmt : CoverNegCheck.ReadsOfQuoteStmt` (derived from `readsOfQuoteStmt`).
4. `Expected` statements share these primitives with the Tools file (not re-spelled): Cover2's `MentionsPh`/`LetReach`/`LetEdge`/`PhInRange`, Cover3's `LooseOcc`/`MentionPos`,
   `FStep`/`FReach` (constructor types are checked separately), `ShapeAgree` (field-wise by `shapeAgree_fields`). `FullInv` and its parts are re-spelled in the Check.

## Checks (Cover3Check, observed in the Pod build)
TYPE 27 compared declarations (aggregation rule: one compared declaration = 1, not log lines; breakdown: 20 theorems via `checkExpected` + 1 theorem whose type is a Prop def, `readsOfQuoteStmt`, via `checkExpectedUnf` + 6 `FStep` constructors via `checkExpectedC`; the 3 iff/field lemmas, 3 scanner-equivalence/negcheck theorems and 2 kernel negatives are not TYPE-compared; AXIOMS lists 29 theorems; earlier note "TYPE 20" counted only the `checkExpected` theorems), MUTANT 6 (`MutLooseMachClose` `c-p`; `MutReadsOfQuoteStmtRev1` no `PhInRange`; `MutLetRange` `≤`; `MutRowCNoNL`; `MutFStepGroup`
without `rs.length = os.length`; `MutRowA3` `≤`) — each a well-typed statement rejected by the same comparer by signature/defeq, **not** a semantic counterexample.
AXIOMS 29 constants standard only; CLOSURE OK (4233 constants, no `sorryAx`/native axiom), 3 negative + 2 clean controls; the 3 intended negative controls (in memory,
`withoutModifyingEnv`) print 3 "declaration uses sorry" warnings (意図した負例 3 件). Kernel negative kept: `c3_example_not_in_range`, plus CoverNegCheck's own.

## Still open / not claimed
- `FReach` is a closure of abstract steps, **not** a trace of the real reader. R-trace (reader steps are `FStep`s with premises met), R-in (input clause / loose-bvar bound of
  the entry body), R-nl (`LetsNoLoose`), R-dom, B3 (memory arg sorts), Q-wit/Q-cmp/Q-snd (`LetQuoteEq` etc.), `resultRange_final`'s `hv` (range at return time),
  `ShapeAgree`, `hb`/`hv` (O10/O11) are premises or unsupplied. Searches found no supplier for these in this tree; that is not a claim they are impossible.
- No real run, `dataOf` success, `GenWF` on real data, corpus, M5 or FG statement is made.

## Clean build
`cv7v-72752f4c` (exit 0, 708 jobs, scoped approved at 72752f4c) is recorded in the `Cover3Check` header. Approval covers Cover3 U-D1/U-D2/U-D3 + audit fix as a conditional intermediate result.
