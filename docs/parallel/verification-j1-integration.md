# J1 fix — INTEGRATED on poc (2026-10-14, ruling item 1 of the second message)

Change: `Sparkle/Backend/CSim.lean`, the `self->` qualifier's token test accepts `$`
(`c.isAlphanum || c == '_' || c == '$'`), with the comment at that place saying why. (Two older comments a
few lines above still say "alnum/underscore"; they are corrected together with the next change of that
file, to avoid one more full rebuild for a comment.)
J1 was a regression of b7dc0ec4 (injective module names) for `private` children in the C simulation /
JIT path: a compile error of the generated C, not a silent wrong result.

Run `j1-int` on the poc tree (cgrun 3 GiB swap 0; exit 0, peak 2.74 GB):
`lake build Tests.AllTests Tests.Compiler.CacheCoherenceProbe Tests.Compiler.DesignCoverageTest` — exit 0;
the tagged-name driver — exit 0; sims writer, module_name, nested_let, subinst_key, optprint — exit 0.

Driver rows on this tree ("C main over the vtable": the generated C compiled with the repository's flags
and run from a C `main` through `jit_vtable()` — NOT the Lean FFI loader):
* the six rows that failed: `priv`, `kw`, `dig`, `alias`, `mem`, `uni` — `csim-cc exit=0`,
  `csim-run c==source T`;
* the real `#sim` on a parent with a `private` child (`simcmd-priv`): Lean ok, `csim-cc exit=0`
  (the generated file compiles; it is not loaded through the FFI by the driver);
* tagged tops and plain rows unchanged (`exit=0`, T); `cfn` / `ckw` / `cjit` still `exit=1` (J2–J4, older,
  fixed separately).
The Lean-FFI end-to-end path (`JIT.compileAndLoad` → `sparkle_jit_load` → `eval_tick`) on a parent with a
private child is a SEPARATE test (`Tests/Compiler/TaggedJitE2ETest.lean`), recorded where it is run.

UNVERIFIED — this is not "all backends": the CUDA emitters (no `nvcc` on this machine), the
`Verilator.of` shim for a tagged TOP (`V<top>.h` vs Verilator's `__024` encoding), vendor / FPGA flows,
designs parsed from external SV with `$` in instance names.
