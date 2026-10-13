# J1 fix CANDIDATE — verified in isolation, NOT integrated (2026-10-14)

J1 (docs/parallel/J-tagged-names.md, measured on poc df990315): the C backend does not compile a parent
that instantiates a module whose name contains `$` — i.e. a tagged module name of commit b7dc0ec4
(`private` declarations, keyword / digit / alias / non-ASCII names). A REGRESSION of b7dc0ec4 for
`private` children in the C simulation / JIT path (`#sim`, `#writeDesign`, `toCJIT`); a compile error,
not a silent wrong result. Through the real command too: `simcmd-priv` on poc — Lean ok, `csim-cc exit=1`.

Candidate: branch `fix/csim-dollar-build` d4524f16 in `~/sparkle-work/wt-cachefix` = poc 02b20934 + ONE
change, `Sparkle/Backend/CSim.lean` (the `self->` qualifier's token test):
`c.isAlphanum || c == '_'` → `c.isAlphanum || c == '_' || c == '$'`.
`poc/roundtrip-proof` does NOT contain it. cgrun 3 GiB swap 0. GitHub CI: 0 runs.

Run `j1-iso` (exit 0, peak 2.75 GB): `lake build Tests.AllTests Tests.Compiler.CacheCoherenceProbe` —
exit 0; the tagged-name driver — exit 0; `writer_sim`, `module_name_sim` — exit 0.

| row (driver) | poc: csim-cc / csim-run | candidate: csim-cc / csim-run |
|---|---|---|
| `priv`, `kw`, `dig`, `alias`, `mem`, `uni` (a parent instantiating a tagged module) | exit 1 / no trace | exit 0 / `c==source T` |
| `simcmd-priv` (the real `#sim`) | exit 1 | exit 0 |
| `privself`, `kwself`, `digself`, `unibind`, `regnext` | exit 0 / T | exit 0 / T |
| `cfn` (J2), `ckw` (J3), `cjit` (J4) — older C-emitter collisions | exit 1 | exit 1 (unchanged, as intended: not addressed) |

Emitted C text poc vs candidate: byte-identical for the rows without a tagged INSTANCE (`regnext`,
`unibind`, `cfn`, `ckw`, `cjit`, `privself`, `kwself`, `digself`); for `priv` / `kw` / `mem` the only
differing lines are the instance references, now `self->_tmp_inst_Sp$D$…`.

NOT claimed / not done: the repository's JIT loader end to end through the Lean FFI (the driver compiles
with the repository's flags and runs through the same vtable from a C `main`); designs parsed from
external SV with `$` in instance names (the same line would apply); J2–J5 (older: function-name
ambiguity `sparkle_<m>_<verb>`, a module named like a C keyword, a module named `jit`, and the `#sim`
output path by last name component — `simcmd-uni2` on poc: "`tnz_.Sim.jitCppPath` has already been
declared" after the file was written); CUDA emitters (no `nvcc`); the `Verilator.of` shim for a tagged
TOP (`literal-top-header F`).
