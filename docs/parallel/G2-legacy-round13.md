# G2 — worker B, round 13 (branch `par/g2-legacy-13`, base `5fc968ab`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §42–§45.

This round is PARTIAL: item 2 is done, item 3 is answered with the missing
laws named and one lemma, item 1 is NOT done (plan only).

## 42. Item 2 — `hnosub` narrowed; what `hmap` needs

`LeafDom.inlineAt` asked its dispatch premise of every recursive translator;
the proofs instantiate it only at `translateFuelFix translateStep fuel`. The
constructor now asks `∀ fuel, ReachesUnfoldAt (translateFuelFix
translateStep fuel) …` (weaker premise, larger domain, same conclusions), and
`useDbl_output`'s `hnosub` is `∀ id cache bools bits fuel, NoSubModule
(translateFuelFix translateStep fuel) …`.

What is really needed for `useDbl`: ONE translator, `translateFuelFix
translateStep (translateFuelLimit - 1)` (the leaf is translated at the full
fuel; its step hands that translator to the fallback; the unfolding is in
`LegacyDom`). The constructor keeps every fuel because a nested inline leaf
uses one fuel less per level; a one-level statement at the single fuel is a
small separate theorem, not written.

`hmap` (and `hnosub`) stay quantified over the variable and the cache: both
are outputs of the run (existential in the conclusion), so a hypothesis
about "the run's own" variable needs the walk to hand them out together with
the facts — i.e. to move these premises into the facts the telescope
delivers (H1). The quantifier over `bools` / `bits` is not real: `prepare`'s
context does not depend on them.

## 43. Item 3 — `MemoHit`: the law does not exist

`Tools/ShippingChildInv.lean`: `sparkleSubModuleCache` is `SideRef.subModule`
(line 73) only — the frame class of the three tracked cells. `RefLaws` has
value functions and get/set laws for `sparkleChildCache`, `sparkleChildSynth`
and `sparkleSynthDepth`; none for the memo.

`Tools/ShippingLegacySemMemo.lean` (new): `MemoLaws` (`mval`, `memoGet`,
`memoSet` — the missing laws, as a parameter in `RefLaws`' style) and
`memo_miss_after_reset` (the read after a reset misses, given the frame of
`mval` between the two worlds as a hypothesis).

Still needed for the statement one level up: a frame class for `mval`
(`Framed` cannot be reused: it contains the memo's own writes); the walk of
`synthesizeCombinationalCoreWith` in `RunsTo` form; and `legacy_entry_walk`
in `RunsTo` form, because `MemoHit` as stated (`MReturns`: SOME run of the
read) cannot be refuted by a heap law.

## 44. Item 1 — H1: not done

What it takes, in order (none written):

1. a `RunsIn` calculus: `RunsIn.bind`, `.pure`, `.liftMetaM` (to `MRunsIn`),
   `.tryCatch` — the `Returns` lemmas with the context kept;
2. `legacy_entry_walk`'s tail (after the telescope) in `MRunsIn` form, and
   the telescope premise as `MRunsIn (lambdaTelescope body k) mctx r → ∃ xs
   inner mctx', P mctx' xs inner ∧ MRunsIn (k xs inner) mctx' r`
   (Meta-library fact; `P` says what `mctx'.lctx` holds for `xs`);
3. the binder walk for one binder: `getDecl_runsIn` (written, round 12),
   then two oracle premises on the binder's type — `isSignalBinderType`
   leaves the builder state; every successful run of `inferHWTypeFromSignal`
   on it returns `.bitVector n` and leaves the builder state — and a third
   outcome to exclude or keep: the `try` around `inferHWTypeFromSignal`
   returning `false` (the binder is then SKIPPED, no port);
4. `splitReturnLeavesStep` on a non-structure Signal result.

## 45. Hypotheses of `useDbl_output` after this round

`htele`, `hmap`, `hplain`, `hnosub` (narrowed), `hunfE`, the run `hr`;
conclusion `MemoHit ∨ …` (unchanged).
