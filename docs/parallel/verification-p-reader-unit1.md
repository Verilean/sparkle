# Worker P (fix/reader-p1): integration of unit 1; the gate FAILED; switch NOT taken

Integrator, 2026-10-14. Base: poc `4868fa8d`. Worker commits applied: `887336b6` (unit 1, rawNode
pair-matcher arm), `d24022ae` (prodMatcherArity? OLD shadow + test). `1824625b` (the gate,
`Tools/ShippingReaderMatcherArityArray.lean`) was built and FAILED; per the gated plan the switch
(`74524aa6`) and the files that need it (`ffb38e98`, `a3d4ff16`) are NOT taken. `389a34dc` (worker record,
which describes the switch) is not taken either; this file is the record of what was integrated.

## Measured (cgrun, 3 GiB, swap 0, `-j 1`)
Run `p-before` (as written by the worker):
* `Tools.ShippingReaderRawNodeArm` — FAILED: `Option.noConfusion` arms of `peelC_length` (type mismatch
  under this toolchain's `noConfusion` signature) and `split` on `rawNode`'s outer `match`.
* `Tools.ShippingReaderMatcherArityArray` (THE GATE) — FAILED: `split` at `stepOldP_eq` (267).
* `Tools.ShippingReaderMatcherArityOldShadow`, `Tests.Compiler.ReaderMatcherArityOldShadowTest`,
  `Tests.Compiler.ReaderMatcherArityShadowTest`, `Tests.Compiler.ReaderDigestTest` — exit 0.

Cause of both `split` failures (measured in scratch files): Lean v4.32.1 cannot generate the equation
lemmas / splitter of these matchers — `rawNode.match_15` and the copy `stepOldP.match_1` (name-literal
plus array-literal patterns): "failed to generate equality theorems for `match` expression". Elaborating
the copy with `backward.match.sparseCases false` does NOT help (also measured).

Integrator fix of unit 1 (no statement changed): `match15_three` — the outer matcher at a
three-argument constant node is its sixth alternative, proved on the matcher's definition (unfold it and
the four `_sparseCasesOn` auxiliaries, split the name into components, `split` the string/size `dite`s);
`rawNode_pairArm_eq` / `rawNode_pairArm_noMatch` use it (`rw [h1, h2, match15_three]; simp only [hk]`);
the `noConfusion` arms became `simp [peelC] at h`. Run `p-arm`: exit 0.

Axioms (`#print axioms`): `match15_three` [propext]; `rawNode_pairArm`, `rawNodePairArmGoal_holds`,
`rawNode_pairArm_noMatch`, `rawNode_pairArm_peel_none` [propext, Quot.sound]; `rawNode_pairArm_some`
[propext, Classical.choice, Quot.sound].

Shadows BEFORE the switch (kept outputs):
```
PRODOLD WHICH: old=verbatim copy (partial) compiler=partial T=goT exprEqv
PRODOLD GRID: calls=79 old returned=7 old!=compiler=0 old!=T=0
PRODOLD SWEEP: constants=260632 old returned=1893 old!=compiler=0 old!=T=0
PRODARITY GRID: calls=79 old returned=7 disagreements=0 structural test differs=0 prediction misses=0 pieces nodes=3341 pieces disagreements=0
PRODARITY SWEEP: constants=260591 old returned=1893 under the roots=595 disagreements=0 structural test differs=0 …
PRODARITY PIECES: definitions=640 nodes=443914 disagreements=0 not compared=0
```

## Status
* Unit 1 (`RawNodePairArmGoal`) PROVED about the real `rawNode`; standard axioms.
* `prodMatcherArity?` switch-over: NOT made. The array/structural agreement is NOT proved; the gate goes
  back to worker P with the cause above and the technique of `match15_three`. The compiler is unchanged.
* Reader tally unchanged by the switch: projChain switched; `prodMatcherArity?` still partial.

## Round 3: the gate BUILT, the switch-over MADE (2026-10-14, later)
Worker P round 3 (`fix/reader-p3`): 38e07d6e (gate proof rewritten: `by_cases` on the first arm's shape;
`Tools/ShippingSparseCasesTac.lean`: `dsimp_sparse_aux`, `unfold_matchers_aux` read the auxiliaries off the
goal), aa4c79de/ad8c3b9c/ded4e182 (= 74524aa6, ffb38e98, a3d4ff16), 1ec45626 (`match15_three` without the
removed `go` auxiliaries' names).
* Gate run `p3-gate`: failed as written (`set_option … in` after docstrings; `stepOldP_none`: `split`
  had already destructured the list, the later `rcases` names did not exist; `generalize_proofs` is
  Mathlib-only). Integrator fixes: options before docstrings; the remaining branch (`Prod.casesOn`,
  `size = 5`) by pinning the list to five elements, then constructor cases of the 4th, 5th and its body
  (`rfl`; the shape contradicts `hL`). Exit 0. Commit 9314c051.
  Axioms: `getAppArgs_eq`, `stepOldP_none`, `stepOldP_shape` [propext, Quot.sound]; `stepOld_eq_step`,
  `goT_oldSol`, `old_unique` [propext, Classical.choice, Quot.sound].
* Switch + theorems: commits 9b86eb38 (compiler: `prodMatcherArity?` a plain def via
  `MachProdMatcher.goS`; `match15_three` reads the auxiliaries off the goal) and 3f1e33a0
  (`…MatcherArityReal`, `…RawNodeCanon`). Built jointly (the intermediate commit not alone), run
  `p-switch` (`-j 1`, peak 2.64 GB): RawNodeArm, Real, Canon, OldShadow test, PRODARITY shadow,
  ReaderDigestTest, `Tests.AllTests` + `DesignCoverageTest`: all exit 0.
  ```
  PRODOLD WHICH: old=verbatim copy (partial) compiler=total T=goT exprEqv
  PRODOLD GRID: calls=79 old returned=7 old!=compiler=0 old!=T=0
  PRODOLD SWEEP: constants=260651 old returned=1893 old!=compiler=0 old!=T=0
  PRODARITY GRID: calls=79 old returned=7 disagreements=0 structural test differs=0 prediction misses=0 …
  PRODARITY SWEEP: constants=260610 old returned=1893 … disagreements=0 structural test differs=0 …
  PRODARITY PIECES: definitions=640 nodes=443914 disagreements=0 not compared=0
  ```
  Reader digest: before (run `p-before`) vs after: 520 lines each, diff EMPTY (as predicted).
  Census 134 declarations, 133 covered (unchanged).
  Axioms: `real_go_oldEq`, `real_go_unique`, `prodMatcherArity_eq`, `prodMatcherArity_fun`, `real_canon`,
  `real_old`, `rawNode_canon`, `rawNode_canon_some` [propext, Classical.choice, Quot.sound].
* What is kernel-checked vs measured: kernel — the old source equation (array form) has exactly one
  solution, the total walk; the compiler's new function is that walk. Not kernel-checked (as for
  projChain) — that the OLD compiled `partial` function satisfied its source equation; the shadows measure
  agreement on 79 grid calls and a 260k-constant sweep.
* Reader tally: projChain and `prodMatcherArity?` switched; the other partial readers open.
