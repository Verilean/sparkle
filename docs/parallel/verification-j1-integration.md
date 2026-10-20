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

## The real JIT path, end to end through the Lean FFI (run `jit-e2e`, poc 31354b57 + the test)

`Tests/Compiler/TaggedJitE2ETest.lean` (worker K, file unchanged, first attempt): a parent with a `private`
child; the real `#sim` at elaboration; at run time `JIT.compileAndLoad` → `cc` with the repository's flags
→ the extern `sparkle_jit_load` (`c_src/sparkle_jit.c`: dlopen + `dlsym "jit_vtable"`); 16 cycles through
the typed wrapper (`step` = `setInput` + `evalTick`) and 16 through the raw FFI
(`setInput` / `eval` / `getOutput` / `tick`), each compared with the source function.
Executable `tagged-jit-e2e-test` (new `lean_exe`), MEASURED:
```
TAGGEDJIT: cycles=32 mismatches=0 tagged-member-in-C=true []
✓ tagged JIT e2e: the C text has the tagged instance member behind self->
✓ tagged JIT e2e: JIT == source on 32 cycles (typed wrapper and raw FFI)
```
The same rows are added to `Tests.AllTests`' `main`; `lake build Tests.AllTests` exit 0 with the import.
This is ONE small design with a combinational private child; it is distinct from the driver's
"C main over the vtable" rows, which never go through `c_src/sparkle_jit.c` or `eval_tick`.
