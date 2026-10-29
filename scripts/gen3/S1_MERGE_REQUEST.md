# S1 merge request: integrate M3 (`par/gen3-induct`) with M2 (`par/gen2-spec`) on a new branch

**Who:** the user. Merging is a user operation; the coder does not run `git merge`.
**Why now:** the agreed serial order of the shared edits is InstClosed (S1) → TopShips R-G (S2) → ChildPortWidths (S3)
(scripts/gen3/UCHILD_PORTTYS_TABLE.md rev3 §R3.3; scripts/gen2/TOP_CONTRACT_REVISION.md rev1.1). S2 and S3 change
`Tools/ShippingGen2Defs.lean`; they must be made on top of a branch that already has M3's `InstClosed`
(third `ShipsRes` conjunct, gen3-induct Defs:127-136). Until S1 exists, only new-file work (NC suppliers, L1-L4,
N-C, etc.) can proceed; the shared edits wait.

## What to merge
| | branch | SHA |
|---|---|---|
| base | `par/gen2-spec` | 695c12f336b2571e4c3d6bd774fd50ddd09fb887 |
| merged in | `par/gen3-induct` | b5be62e6dd2c2bc79b201613b8c89e741e53f6b7 |
| merge-base | — | 1fdbc18d00a89b16b964a76787095e092d1b369e |

Trial `git merge-tree --write-tree` (2026-10-30): `Tools/ShippingGen2Defs.lean` and `Tests/Gen2/PkgCompat.lean`
auto-merge; the only textual conflict is `lakefile.lean` (both sides append `lean_lib` blocks at the end).

## Suggested commands (run by the user)
```sh
cd ~/git/.kjob/gen2-spec            # or any clean checkout of the repo
git switch -c par/gen3-combined par/gen2-spec
git merge --no-ff par/gen3-induct   # conflict only in lakefile.lean
# resolve lakefile.lean: keep BOTH sides' appended lean_lib blocks (union, no duplicates)
git add lakefile.lean && git commit
```
Nothing is pushed; `main` is not touched.

## What the coder does right after (S1 fixes, then verification)
1. `scripts/gen2/GEN2_DEFS.lean.txt`: sync to the merged Defs (gen3-induct never updated it); `cmp` check.
2. Fix the five gen2-spec-only sites that destructure the old two-part `ShipsRes` (git does not report them):
   FitChain:946, OneOut:200, OneOutTop:310, OneOutTopO:303, Arity:83.
3. G-SERVED integration (SERVED_FREEZE rev1 §4.4): `rfl` bridges for the DataBridge copy then delete it, add the `.comb`
   case to `Pkg.traceX`, post imports F1.
4. Issue-linked focused builds at the exact S1 SHA from a clean worktree for every accepted unit on both branches,
   then final importers of Defs and AllTests; axioms audit; record every SHA.
Only after S1 is verified: S2 (R-G Defs switch, NC suppliers already in place), then S3 (ChildPortWidths).

## Options
- **(A) Merge now as above (recommended).** Unblocks S2/S3; cost: the coder's S1 fix-up and a full re-verification.
- **(B) Defer.** New-file work continues, but `TopShips` R-G, `ChildPortWidths` and the T1 assembly stay blocked; the
  two branches drift further (more re-verification later).
Reversible: yes (the new branch can be discarded; `par/gen2-spec` and `par/gen3-induct` are untouched).
