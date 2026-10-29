# S4 stage B stop-report: `RunFacts.wid` for one-output parents has no frozen supplier (FOR REVIEW)

- **Issue:** `sparkle-gen2-step`.
- **Branch:** `par/gen2-spec` at 4c0e8b24.
- **Status:** no Lean written.

## What stopped
- **The route.** `oneOut_topShips` is to be assembled as `machine_linked_callsServed1F` → `composedNWn_of_HBF` → `composedNWRegsF_of_composedNWF` → `machine_ships_hierC_run`. It needs `RunFacts (childMap D.modules) b`.
- **The missing field.** The fields `gate`/`ndB`/`self`/`outs`/`rst` come from `core_runFactsHA` (ParentDesignA:494), and `wfB` from `core_linkedWF_ranA` (ParentTailsA:197). **`wid`** (`instOutWidthsOk (childMap D.modules) (declWidth b) b.body = true`) has no supplier.
- **Why the existing supplier doesn't apply.** `core_instOutWidthsOk_ranA` (ParentRunFactsA:566) needs `instFields ≠ []`. It uses `core_callPorts_ranA` (also `instFields ≠ []`) and `hkidW` over `RealChildA` results on the `ran` witness.
- **The named replacement was never frozen.** `core_instOutWidthsOk_oneA` is described in S4_CONSUMER_FREEZE §5 (lines 549-553) in prose only, with no Lean type, and is listed as MISSING (consumer §9, fit §7). By the rule, the implementer stopped instead of inventing its premises.

## The design question
`wid` is about `declWidth b` of the post-processed module on the `ran` witness. `hW : ∀ k, OneOutWidth P p k` speaks about packages `q` linked to the served module through `ServedP (ShipsRes L P)` on the TRACE's `ids`/`cache` witness. The options:
- **(a) Same `ran` witness: a one-output copy of `core_callPorts_ranA` plus a per-call child width fact on `ran`.** The fact is `hkidW1`: for each call `k`, the `RealChildA` result's single output port width equals the parent binder width at `kD + k`.
  - **Where `hkidW1` would come from:** the same `OneOutWidth`-style data, but against `RealChildA` modules instead of packages. It would need its own supplier, or a lemma that a `RealChildA` result's output width is its package's `layout.outs` width (via `ShipsRes`/`ChildShips`'s output-shape conjunct).
  - **Fit with the precedent:** it keeps the existing `ran`-based `core_*` pattern.
- **(b) Link the `ran` witness to the trace witness.** Show that for the same run the closing's `ids`/`cache` and port names match the trace's, so `hW` can be used directly on `ran`.
  - **Status:** the fit freeze already recorded "nothing supplies a match of `k` across the two witnesses" for a rejected variant. No such link exists today.
- **(c) Make `wid` (or `instOutWidthsOk … b.body = true`) an explicit premise of `oneOut_topShips`.** This changes the frozen stage-B telescope, by adding a run-level premise. Its supply would be a separate obligation. NOT recommended: it moves a compiler-checkable fact into an assumption.

**Recommendation: (a).** It keeps everything on one witness (`ran`), mirrors the accepted `core_instOutWidthsOk_ranA` structure, and reduces the new obligation to a per-call width fact about the served child. That fact plausibly follows from `ShipsRes`'s `ChildShips` output conjunct (`mc.outputs = outsC.map …`) plus `OneOutWidth`. I'd freeze:
- `core_callPorts_oneA` (exact type modelled on `core_callPorts_ranA` with `instFields = []`);
- `hkidW1` (exact type);
- `core_instOutWidthsOk_oneA` (exact type);
- the lemma `hkidW1_of_shipsRes` connecting it to `hW` + `ShipsRes`, if the `RealChildA` results and the served `ShipsRes` results can be identified on the same run (stop if not).

## Effect
- **Stage B waits** for this decision.
- **Unchanged:** stage A, the fit chain and every accepted result. No FG/guarantee change unless (c) is chosen.
