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
