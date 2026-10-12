# G2 — worker B, round 12 (branch `par/g2-legacy-12`, base `5c8fe4ef`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §37–§41.

## 37. `LegacyDom.inline` restated — what changed and what it no longer claims

`Tools/ShippingLegacySemContract.lean` (edited):

* new `ReachesUnfold rec ctx e`: every successful run of the fallback on `e`
  is a successful run of the translator on an unfolding of `e` (same hint,
  same name flag, `isTopLevel = false`, same states, same wire);
* `ReachesInline.unfold : ReachesInline rec ctx e → ReachesUnfold rec ctx e`;
* the second premise of `LegacyDom.inline` is now `∀ rec, ReachesUnfold rec
  ctx e` (was `∀ rec, ReachesInline rec ctx e`);
* `LegacyDom.inline_of_reachesInline` — the OLD constructor, as a theorem.

The new premise follows from the old one, so the domain did not shrink and
every theorem about `LegacyDom` has the same statement. **What a derivation
by `inline` no longer records**: that the wire was produced by a run of
`Rec.tryInlineUnfold`; only that it is the wire of a translation of an
unfolding. No proof used the stronger fact.

Consumers migrated: `legacy_fuel_contract` (inline case re-proved directly;
`LegacyArm` / `legacy_step_contract` are kept, unused by it),
`legacy_fuel_protect` / `legacy_fuel_order` (`Tools/ShippingLegacySemOrder.lean`),
`useDbl_output_r11` (the round-11 theorem, renamed; its `hreach` is now
`ReachesUnfold`).

## 38. The flags the leaf lemmas use — checked — and the contract at them

`emitLeaves_structure`, `emitLeaves_correct`, `emitLeaves_from_ports`,
`emitLeaves_postReady_at` use the leaf's `Contract` at exactly
`.frame "out" false true` and `.sem "out" false true` (lines 66, 91, 157,
170 of `Tools/ShippingUnifiedEntrySoundness.lean`); nothing else.

* `Tools/ShippingLegacySemLeafAt.lean` (new; namespace
  `Tools.ShippingUnifiedEntrySoundness`): the four lemmas from the leaf's
  `ActionSpec` at those flags (`…_spec`). Generated from the originals by two
  substitutions.
* `Tools/ShippingLegacySemHarnessAt.lean` (new): `harness_sound_spec`.
* `Tools/ShippingLegacySemLeaf.lean` (new): `ReachesUnfoldAt`, `LeafDom ctx
  inputs hint named` (an expression of `LegacyDom`, or an inline call AT
  THESE FLAGS whose unfoldings are leaves at the same flags),
  `leaf_translate_spec`, `leaf_translate_order`, `leaf_output`,
  `leaf_entry_output_walked`.

`LeafDom` does NOT give a `Contract`: a legacy call under a certified node
(translated at the cacheable flags) is still not covered; that needs the
shim's hit validated (variant B).

## 39. H2 and H3 for `useDbl`

* H2 → `dbl_reachesAt`: from `HasMappedFVar` (kernel-opaque), `PlainHead`,
  `NoSubModule`, by `plain_call_reaches` at `named = true`.
* H3 → `hunfE` (every unfolding the oracle returns is the quoted `x + x`)
  + `dbl_unfold_dom` (the quoted term is in the domain at `x + x`)
  + `useDbl_input` (the prepared setup maps the binder to its value).
  `hunfE` cannot be proved: `InlineUnfolds` is a run of `unfoldDefinition?`
  in SOME environment (`MReturns` quantifies the Core state); it is
  reflection of the oracle. The test logs whether the oracle's result on
  `dbl x` in the test's environment equals the quoted term (`hunfE
  EVIDENCE`). If that log says `false`, the shape in `hunfE` (the operator
  as `binE dom 8 .add`, the domain as an expression) is wrong and must be
  corrected from the logged expression — the theorem stays valid but its
  hypothesis would be false of the real run.

## 40. H1: the run predicate only

`Tools/ShippingLegacySemRunIn.lean` (new): `MRunsIn m mctx a`, `RunsIn c
mctx ctx s a t` (the `Meta.Context` exposed), their refinement of
`MReturns` / `Returns`, `MRunsIn.bind` (same context for both parts),
`MRunsIn.pure`, `getLCtx_runsIn`, `getDecl_runsIn` (the returned declaration
is `mctx.lctx.find? id`, or the error path ran successfully — not walked).

NOT done: the telescope in this form, the binder walk, `splitReturnLeavesStep`.
H1 of `useDbl_output` is unchanged.

## 41. Hypotheses of `useDbl_output` after this round

`htele` (H1, unchanged), `hmap`, `hplain`, `hnosub`, `hunfE`, and the run
`hr`; conclusion `MemoHit ∨ …`. Verbatim in the test file.
