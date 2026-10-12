# G2 — worker B, round 11 (branch `par/g2-legacy-11`, base `3a680402`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §32–§36.

## 32. `HarnessSound` is a theorem (`Tools/ShippingLegacySemHarness.lean`)

`harness_sound_at` / `harnessSound : HarnessSound`. The proof text is
`synthesizeMixedCertified_term_sound_at`'s (lines 646–755), generated from it
by a script: the steps that produce the contract and the order from the
quoted term are removed, the two facts are hypotheses, the value is any
`Value` of positive width. No other step changed.

## 33. Protection and order over arbitrary leaves, and on `LegacyDom`

A gap found on the way: the order proof of a certified node needs, of its
children, the contract, the ORDER and also PROTECTION (`ActionProtect`), and
`fuel_protects` / `fuel_orders` exist only for terms whose leaves are input
binders. `fuel_contract_leaves` had no protection / order counterpart.

* `Tools/ShippingUnifiedProtectionLeaves.lean` (new, in the namespace
  `Tools.ShippingUnifiedProtection`): `fuel_protects_leaves`,
  `fuel_orders_leaves` — the two certified inductions over arbitrary leaf
  expressions, each leaf with its meaning, contract (every fuel and
  environment), protection and order. Generated from the certified proofs by
  five textual substitutions (listed in the file header), 329 + 317 lines.
* `Tools/ShippingLegacySemOrder.lean` (new): `legacy_fuel_protect`,
  `legacy_fuel_order`, `legacy_translate_protect`, `legacy_translate_order`
  by induction on `LegacyDom`. The inline arm's case is direct: the step on
  the call IS a run of the translator on an unfolding, same states, same
  wire.

## 34. The entry arm, walked (`Tools/ShippingLegacySemEntryWalk.lean`)

`legacy_entry_walk`: for `synthesizeFromConst … [] false cfe (.defnInfo dv)`
(front end on with the three gates declining, or off), a successful run is a
`MemoHit` or a run of `bindInputsLegacy [] false xs 0 (emitLeaves …
leaves.toList none 0)` from the fresh state, finished by `finishSynth`
(module equation + legal name). `legacy_entry_output_walked`: the output
statement from it, with `harnessSound`, `legacy_translate_contract`,
`legacy_translate_order`.

Premises, classified:

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` (gates decline; only with the front end on) | reflection of the environment |
| `TelescopeSpec` (a run of `lambdaTelescope body k` is a run of `k xs inner`) | a fact about Lean's `Meta` library — neither reflection nor heap |
| `BinderWalk xs bs ids` | the run; NOT walked — and not statable with `Returns`: `getDecl` reads the local context the telescope installed, which `Returns` / `MReturns` hide (needs-definition, then needs-walk) |
| the leaves (`splitReturnLeaves inner` returns `[("out", leaf)]`) | the run (oracle); needs-walk of `splitReturnLeavesStep` |
| `MemoHit` | NOT a premise: the second outcome, in the conclusion. Excluding it at the outermost entry is a heap fact of the caller |

Finding: with the certified front end ON, `useDbl` is NOT a fallback input
(`entryConst` unfolds `dbl`; a certified gate takes it). The fallback arm is
reached with the front end off; the walk covers both.

## 35. `useDbl_output` and the distance to the acceptance unit

`Tests/Compiler/LegacySemInstanceTest.lean`, `useDbl_output`: a successful
run of the entry on `useDbl` (legacy front end) is a memo hit or
`RawValueAt 8 [(x, bits 8)] m initial mems (x + x).toNat`.

Hypotheses left, exactly:

* **H1** `htele`: `TelescopeSpec` + `EntryFacts` (`ids` distinct, one per
  binder; `BinderWalk`; the single leaf).
* **H2** `hreach`: `ReachesInline` at the prepared context for EVERY hint and
  flag. Walked (round 9, `plain_call_reaches`) for `named ∨ top` from
  `HasMappedFVar` (kernel-opaque `Expr.find?`), `PlainHead`, `NoSubModule`.
  The entry uses `named = true` only, but `Contract` (hence
  `LegacyDom.inline`, hence the harness lemmas) quantifies all flags, and at
  the cacheable flags today's shim can return an unvalidated hit.
  Also a form mismatch: `plain_call_reaches` concludes "a run of the
  translator on an unfolding", `ReachesInline` asks "a run of
  `Rec.tryInlineUnfold`" — the domain's constructor asks more than its proof
  uses.
* **H3** `hunf`: the unfoldings of `dbl x` are in the domain at `x + x` at
  the prepared inputs (reflection of `unfoldDefinition?` + the input lookup
  of `prepare` + `LegacyDom.cert`).

Plus the second outcome `MemoHit`.

## 36. Next, in order

1. Restate the inline constructor of `LegacyDom` with the conclusion the
   proofs use (a run of the translator on an unfolding) — then
   `plain_call_reaches` feeds it — and a flag-restricted contract through
   `emitLeaves_from_ports` / `emitLeaves_postReady_at` (they use the leaf's
   contract at `("out", false, true)` only, to be checked), so H2 reduces to
   `HasMappedFVar` + `PlainHead` + `NoSubModule`.
2. H3: the prepared input lookup (`prepare` on one `bits 8` binder), and the
   unfolding as a quoted term.
3. H1: a run predicate that exposes the `Meta` local context; then the
   binder walk and `splitReturnLeavesStep` for a scalar result.
