# Finding I fix PROPOSAL — verified in isolation, NOT integrated (2026-10-13)

Candidate: branch `fix/singleout-build` e0de3b06, tree `a348dcf80bc282971775f37208e3e9588621bba9` = poc 0a0a4f71 + worker A's
`fix/singleout-nested` b0039f0c (cherry-picked, no conflict) + one integrator fix in a test's header
comment. Built ONLY in the isolated worktree `~/sparkle-work/wt-cachefix`; cgrun 3 GiB swap 0.
`poc/roundtrip-proof` does NOT contain the fix. It awaits a ruling
(docs/parallel/open-rulings-2026-10-13.md, item 2). The finding and the reachability table are in
`docs/parallel/I-singleout-stale.md` on the candidate branch.

| run | what | result |
|---|---|---|
| `i-fix` | `lake build Sparkle` + the three changed proof files (ShippingChildKeeps, ShippingMemoLaws, ShippingMemoLawsWith) | exit 0, 304 jobs, FIRST ATTEMPT (blind proof follow-ups built as written); peak 2.75 GB |
| `i-fix` | `Tests.AllTests` + SingleOutNestedFixTest, SingleOutHitTest, NestedLetCacheTest, SubInstanceKeyTest | one failure: the new test, "unterminated comment" (`<T/F/->` in its header opens a nested comment) |
| `i-fix` | sims nested_let, subinst_key, writer, optprint, module_name | each exit 0 |
| `i-fix2` | the same build after the comment fix | exit 0, 1325 jobs; peak 0.82 GB |
| `i-fix2` | the OLD probe `SingleOutStaleProbe` on the candidate | exit 1 AS EXPECTED: "the two modules are EQUAL" |
| `i-fix2` | the 28-file sample on poc (fresh, `pnew`) vs candidate (`inew`), `compare_outputs.py` | statuses equal; 27 identical, 2 "different" = the tree path inside two missing-olean messages; NO emitted-text difference |

Measured on the candidate (`SingleOutNestedFixTest`):
```
SINGLEOUTFIX A: returned=T hIrr insts=1 stmts=3
SINGLEOUTFIX B: returned=T hIrr insts=1 stmts=3
SINGLEOUTFIX RESULT: equal=T
SINGLEOUTFIX pOuter: returned=T pMid nested found=T hIrr insts nested=1 alone=1 nested==alone=T
SINGLEOUTFIX pMach: machine shape=F real=T hIrr insts real=1 cold=1 => stale hit on a real command=F
SINGLEOUTFIX FIXED: nested entry ran=T restores single-out=T => fixed=T
```
So with the fix the constructed state of Finding I gives the same module in both runs; the two rows on
REAL commands show no stale hit (they are predicted to show none on poc too — not measured on poc).

NOT claimed: that Finding I is reachable by a real compile (by reading it is not); that any shipped design
changes (sample only, 28 files); that the legacy route becomes deterministic (the legacy memo and the type
cache are still read at nested entries); the corpus.
