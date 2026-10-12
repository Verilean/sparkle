# B, round 2 — memo census, two more outer theorems (branch `par/b-2`, base `par/b-1` = `a606c28a`)

**Nothing here was built.** Continuation of `docs/parallel/B-memo.md`; the
wire-width item is in `docs/parallel/B-wirewidth.md`. Everything under
`RefLawsM` is under the EXTENDED trust base of B-memo.md §7 (no new
assumption is added in this round); none of it completes the general theorem.

## 1. The memo read, measured (`Tests/Compiler/MemoHitCensusTest.lean`)

Logs only; never throws.

**Can the hit be observed directly?** No, not from inside the process: the
entry builds `logProf` itself from `IO.getEnv "SPARKLE_PROFILE"` (Elab.lean
5400–5407); `synthesizeCombinationalCoreWith` has no logger parameter. The
hit branch (5311–5313) logs `[profile] synthesizeCombinational {declName}
MEMO HIT` to stderr and `/tmp/sparkle-profile.log` only when that variable is
set. Outside check: run the test with `SPARKLE_PROFILE=1` and `grep -c "MEMO
HIT" /tmp/sparkle-profile.log`.

**What the test does instead.** Every nested synthesis starts at the ref
`sparkleChildSynth`. For the duration of one run the test replaces it by a
wrapper that reads the two caches and then calls the REAL `synthesizeChild`
(the entry, translator and memo are the real ones). Per nested request for
`n`: `inCache` (child cache holds `n`), `inMemo` (memo holds `n`), `cycle`
(`n` is in progress — the wrapper's stack, outermost declaration at the
bottom), and the gate route of `n`'s entry constant.

**Why zero is conclusive.** A read returns an entry for `n` only if one is
there; entries for `n` come only from runs of `synthesizeFromConst` on `n`;
the memo does not shrink inside a depth-0 run. A nested hit on `n` therefore
needs `inMemo` at the request (an earlier run completed) or a `cycle` (one
completes before the read); a hit of the outermost run needs a nested request
for its own name (a `cycle`).

* `hits` = requests with `¬inCache ∧ inMemo` on the `legacy` route (the read
  is reached with the entry present: certain);
* `possible hits` = the same on the `machine` / `mixed` route (a hit iff the
  machine synthesis declines and falls through);
* `by-name cycles`.

**Population.** The candidate enumeration of `LegacyArmCensusTest` (Signal-
valued definitions of the imported `IP` / `Examples` / `Tests` modules, name
order, cap 400), all routes except `certified`, legacy first, then machine,
then mixed. `Tests/Compiler/HierBindsCensusTest.lean` is not on this branch
(it lives on main); the instance parents here are whatever the machine /
mixed routes of this population contain.

**Expected log lines**

```
MEMOHIT CENSUS: N runs of the shipping entry (… legacy-route, … machine-route, … mixed-route candidates; R returned; … not run: time budget; … ms); nested requests Q, answered by sparkleChildCache C; hits 0 []; possible hits (memo entry present, machine or mixed route) 0 []; by-name cycles 0 []
WIREWIDTH UNDECLARED: …  0 []
WIREWIDTH DIGEST: R returned declarations, combined digest H
WIREWIDTH DIGEST, per declaration (name=top/design): …
```

Expected by reading: `hits 0`, `possible hits 0`, `cycles 0`. If `Q = 0` the
population has no child synthesis and the measurement says nothing about
nested reads (then add instance parents). If all three are 0 with `Q > 0`:
the read was dead on this population — a measurement, not a proof; the
proposal "delete the read" stays a proposal.

## 2. `tuple_entry_output_outer`, `useDbl_output_outer`

`Tools/ShippingLegacySemMemoOuter.lean`:

* `tuple_entry_output_at` (first disjunct `(L.mval w0).get? declName = some
  (m, d)`), `tuple_entry_output_miss`, `tuple_entry_output_outer` — the old
  proof with `list_entry_outputDN_at`. The outer form: for `RunsTo
  (synthesizeCombinationalCore declName [] false) … w0 (m, d) w1`, premises =
  `tuple_entry_output`'s + the boundary (`L`, `L.dval w0 = 0`, `L.quiet w0`)
  + `EntryConstIs` + `mixed` at the run's instance predicate. `hchain` (with
  `WireWidthReads`, `ArgRunsBody` inside) is unchanged.
* `one_binder_entry_output_bound_at` — the old proof with
  `legacy_entry_walk_start`, either front end.

`Tools/ShippingMemoLawsWith.lean`: `outer_reset_reaches_with` —
`outer_reset_reaches` for `synthesizeCombinationalCoreWith translate declName
[] false cfe` (any translator, either front end; the same proof text), and
`entryConst_off` (`entryConst false false [] ci … = ci`). Needed because
`useDbl` reaches the legacy arm only with the front end OFF.

`Tests/Compiler/LegacySemMemoOuterTest.lean` (the declaration `useDbl` lives
in a test file): `useDbl_output_at`, and

```lean
theorem useDbl_output_outer (L : RefLawsM mref cref) {dv m d xTy} {w0 w1}
    (h0 : L.dval w0 = 0) (hq : L.quiet w0)
    (hci : ∀ v1 ci v2, RunsTo (getConstInfo ``useDbl) mctx mref cctx cref v1 ci v2 →
      ci = .defnInfo dv)
    (htel …) (hbody …) (hinf …) (hinfT …) (hres …) (hmap …) (hplain …) (hnosub …) (hunfE …)
    (hr : RunsTo (synthesizeCombinationalCoreWith
      (fun e hint top named => translateExprToWire e hint top named)
      ``useDbl [] false false) mctx mref cctx cref w0 (m, d) w1) :
    ∃ id cache, ∀ bools bits initial mems, Admissible … →
      RawValueAt 8 useDblBinders m initial mems (bits id 8 + bits id 8).toNat
```

With the front end off no gate is asked, so no `EntryConstIs` about an
unfolding: the link is `hci` alone (every read of the declaration returns
`.defnInfo dv`). The audit of the eight new theorems is in the same test
(throws on a non-standard axiom).

## 3. Not done

* `fst_entry_output`, `list_entry_output(D)`, `SoCState_fetchPC_output`,
  `SHA256Out_done_output`, `useDbl2_output`, `useAdd2_output` in outer form
  (same recipe; the instances are corollaries of the class theorems).
* Everything listed in B-memo.md §6 (machine-arm fall-through, the full
  entry, `MemoSound`, constant stability).

## 4. Unverified, most likely to fail first

1. Everything of round 1 that this round's proofs call (`legacy_entry_walk_at`
   first).
2. `MemoHitCensusTest` (compiled code): the wrapper's `IO`-ascribed ref
   operations inside `MetaM`, the `try … catch` re-throw, `Sparkle.IR.Reorder.stmtReads`
   (the import `Sparkle.IR.ReorderInvariance`), the tuple pattern `some (dg, und)`.
3. `outer_reset_reaches_with`: the copy of the round-1 proof with `translate`
   and `cfe` variables (the unfold of `synthesizeCombinationalCoreWith` alone).
4. `useDbl_output_outer`: `rw [entryConst_off] at hrun` (metavariable
   arguments), `rw [hci …] at hrun`, the positional `[] false false`.
5. `entryConst_off` (`rfl` on a Boolean `if`).

## 5. Build queue (after round 1's five)

6. `Tools.ShippingMemoLawsWith`
7. `Tools.ShippingLegacySemMemoOuter`
8. `Tests.Compiler.LegacySemMemoOuterTest` (imports `Tests.Compiler.LegacySemInstanceTest`)
9. `Tests.Compiler.MemoHitCensusTest` (runs the entry on up to 400 declarations; budget 360 s)
10. `Tests.Compiler.WireWidthStaleTest`

```lean
lean_lib «Tools.ShippingMemoLawsWith» where
  roots := #[`Tools.ShippingMemoLawsWith]

lean_lib «Tools.ShippingLegacySemMemoOuter» where
  roots := #[`Tools.ShippingLegacySemMemoOuter]
```
