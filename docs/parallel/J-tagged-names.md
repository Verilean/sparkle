# Tagged module names through the supported tools (worker J, round par/j-1) — WRITTEN, NOT RUN

Reviewer's ruling 2026-10-14, item 6: confirm that small private / reserved-word / name-collision examples
are accepted on the yosys / Verilator / C JIT paths the repository actually supports; inspect separately the
places that convert names to C identifiers; a tool that is not available is named and left unverified; no
external service, no new install.

Base: `poc/roundtrip-proof` df990315, branch `par/j-1`. Nothing in this document was run: no `lean`, `lake`,
`yosys`, `verilator`, `iverilog` or `gcc` was started. Every outcome below is a PREDICTION from reading and is
labelled so. Nothing under `Sparkle/` was edited.

Result of the reading in one paragraph: the SystemVerilog side keeps tagged names apart (the emitter's
`sanitizeName` is the identity on `ofDecl`'s image, and the two external SV tools are expected to accept `$`).
The C backend does NOT: its `sanitizeName` is also the identity on the image, but the C text built around the
names is not safe for them. **Finding J1 (predicted, reachable from user declarations, supported `#sim` /
`#writeDesign` path): a parent that instantiates a module with a tagged name (`Sp$D$…`: any `private`
hardware declaration, a keyword / digit-initial name, the `a.b` side of an alias pair, a non-ASCII name, a
declaration named like a memory module) gets C that does not compile**, because the member-qualifying pass
splits identifiers at `$`. The failure is an error at C compile time (`JIT.compile` throws), not a silent
wrong result. Three further collisions of the C identifier scheme (J2–J4) and one silent overwrite of `#sim`
output files (J5, known, older than tagged names) are listed with a row each.

## 1. What the names are

`Sparkle/IR/ModuleName.lean` (`ofDecl`, since b7dc0ec4). Image alphabet: ASCII letters, digits, `_`, `$`.

| form | when | example |
|---|---|---|
| plain `N1_…_Nk_last` | every namespace component upper-case-initial alphanumeric (not `SparkleMem`), last component lower-case-initial letters / digits / `_`, result not an SV keyword | `Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth` |
| memory `SparkleMem_{combo\|sync}_{aw}_{dw}` | built memory module of the machine route | `SparkleMem_combo_4_8` |
| tagged `Sp$D$f1$…$fk` | every other declaration | `Sp$D$module`, `Sp$D$1bad`, `Sp$D$__private$IP$Crypto$AESHW$_0$…$synth__aesSbox` |

Wire, port and instance names are not `ofDecl` names: they come from `CircuitM.freshName`
(`Sparkle/IR/Builder.lean:150`): `_gen_<hint>` / `_gen_<hint>_<n>` or `_tmp_<hint>_<n>`, the hint cleaned by
`NameHints.clean` (`Sparkle/IR/NameHints.lean:24`: every character other than a letter, digit, `_`, `$`
becomes `_`). Instance names are `_tmp_inst_<module name>_<n>` (`Sparkle/Compiler/Elab.lean:6747, 6763,
8607, 8669`), so **an instance of a tagged module has `$` in its instance name**.

## 2. Inventory (by reading)

### 2a. yosys

No Lean code starts yosys (`grep 'cmd := "'` over `Sparkle Tools Tests IP Examples`: `cc`, `verilator`,
`iverilog`, `vvp`, `nvcc`, `make`, `git`, `curl`, `which` — no `yosys`). The Lean files named in the task
mention yosys in comments only.

| place | what it is | supported / tested path? | names that reach yosys | quoting, splicing |
|---|---|---|---|---|
| `Sparkle/IR/Optimize.lean:171, 717` | comments (cell counts, a fold yosys does) | n/a | none | none |
| `Sparkle/Compiler/Elab.lean:8973` | comment (0-width literal yosys / iverilog reject) | n/a | none | none |
| `Tests/Compiler/RtlStructureTest.lean:204, 259, 490, 560, 652` | comments and message text quoting measured yosys numbers | test does not run yosys | none | none |
| `Tests/RoundTrip/IRVerilogIR.lean:25` | comment | n/a | none | none |
| `Tests/Verification/XiangShanDslRoundtrip.lean:15` | comment ("yosys-equiv checked in CI") | n/a | none | none |
| `Tests/Drivers/SvRoundtripMain.lean:46, 49, 130` | comment ("yosys-free") | n/a | none | none |
| `Tools/SVParser/VerifyEmit.lean:26` | comment | n/a | none | none |
| `hw/synth/synth.ys` (= `hw/hw/synth/synth.ys`) | a file of comments: two usage lines, `hierarchy -top BitNet_SoC_HW_4L_4d` / `…_TM_4L_4d` on `hw_unrolled.sv` / `time_muxed.sv` | manual; no script or CI step calls it; no Lean declaration of that name found | hand-typed top names, not `ofDecl` output | typed by hand |
| `fpga/tangNano20k/build.sh:14, 31–33` | `read_verilog -sv build/policy_signer.v; read_verilog -sv policy_signer_top.v; synth_gowin -top policy_signer_top` | supported manual flow (hardware) | every module of `#writeVerilogDesign gen_policyTx` (`build/GenPolicySigner.lean:23`); the hand-written top instantiates `gen_policyTx` (`policy_signer_top.v:24`) | `-top $TOP` in a double-quoted `-p` string; `TOP` is the hand-written wrapper, never a generated name. No generated name is spliced into a script or file name |
| `fpga/tangNano20k/sign_demo_build.sh:12, 26–28`, `sign_msg_demo_build.sh:32–38`, `sign_z_demo_build.sh:32–38` | the same shape; wrappers instantiate `signDemoTop`, `signMsgDemoTop`, `signZDemoTop`; `sign_z_uart_top.v:58` instantiates `Sparkle_IP_Crypto_EcdsaSignMsgSmall_signZSmallDemo` | supported manual flow (hardware) | all modules of the generated `.v`, including children | as above |
| `bench/xiangshan/ci_check.sh:128–133` | `read_verilog -sv $CORPUS/*.sv; hierarchy -top $top; …; equiv_make …` | CI (`.github/workflows/xiangshan-roundtrip.yml`) | module names of the XiangShan corpus and of its re-emission by the SVParser round trip: names PARSED from SystemVerilog, never `ofDecl` | `top=${f%.sv}` — the top is the FILE name; spliced unquoted into a double-quoted `-p` script (a `$` in a corpus file name would be expanded by the shell; no such file exists and `ofDecl` is not involved) |
| `bench/xiangshan/compare_stat.sh:11, 13` | `read_verilog -sv $2/$f; hierarchy -auto-top; synth -run coarse; stat` | manual / CI metric | as above | file names only |
| `docs/tutorial/md/Ch08_Yosys.md`, `Ch09_FPGA.md` | prose | n/a | — | — |

Reading result for yosys: tagged names reach yosys only through the FPGA flows, as CHILD modules inside a
generated `.v` (a `private` helper under one of the four tops would be one). Hand-written wrappers couple to
generated top names in the PLAIN form (`gen_policyTx`, `signDemoTop`, …); they stay plain as long as those
declarations stay public, root-level or under upper-case namespaces. Making one `private` would rename it to
`Sp$D$…` and the wrapper would fail with an unknown-module error (an error, not silent).

### 2b. Verilator

| place | what it is | supported / tested? | names | quoting, splicing |
|---|---|---|---|---|
| `Sparkle/Core/SimVerilator.lean:63–66, 129–146` (`Verilator.of`) | `verilator --cc --build --top-module <top> … --Mdir <objDir>`; writes a C++ shim with `#include "V<top>.h"`, class `V<top>`, `m-><port>`; output `<objDir>/V<top>.so` | supported API, generated by `#sim` / `#simChecked` as `loadVerilator` (`Elab.lean:9423–9433`, `SimChecked.lean`); NO test calls `loadVerilator` or `Verilator.of` (grep over `Tests IP Examples`: 0) | `<top>` = `m.name` of the top = `ofDecl declName`; port names `_gen_…`, `out` | the top name is spliced RAW into a C++ class name, an include file name and a `.so` file name. Process arguments are an array (no shell). `objDir` defaults to `/tmp/sparkle_verilator` for every design (`sparkle_verilator_tb.cpp` is rewritten per call) |
| `verilator/Makefile:19–29`, `verilator/rv32i_soc_wrapper.sv:35`, `verilator/tb_cppsim.cpp:52` | `--top-module rv32i_soc`; the hand-written wrapper instantiates `Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth` | `Tests/RV32/TestFlow.lean:184–228` (`make -C verilator`, skipped when verilator is absent) | all modules of `#writeDesign rv32iSoCSynth` (`IP/RV32/SoCVerilog.lean:80`) as children of the wrapper | hand-written coupling to a PLAIN name |
| `Tests/RV32/JIT*.lean`, `OracleAccuracyTest`, `JITOracleTest` … | use the path literal `verilator/generated_soc_jit.c` — the DIRECTORY name; they run the C JIT, not Verilator | lake exes | C JIT (2c) | path literal |
| `IP/Drone/CoSim/*.cpp`, `Tests/Sparkle16/TestCoSim.lean` | hand-written co-simulation sources | manual | hand-written | — |

Reading result for Verilator: `Verilator.of` with a TAGGED top is predicted to fail to build — Verilator
encodes `$` as `__024` in the class and file names it generates, so `V<top>.h` with a literal `$` is not
there (PREDICTED from the tool's known mangling; the driver row `verilator-cc … literal-top-header` shows
it). An error at build, not silent. Tagged CHILD names stay inside Verilator.

### 2c. C JIT / C simulation backend, and every other name conversion

Where the C is made, compiled and loaded: `CSim.toCDesign` / `toCJIT` (`Sparkle/Backend/CSim.lean:1834–2180,
2362–2396, 2611–2820`) ← `#writeCppSimDesign` (`Elab.lean:9114`), `#writeDesign` (`Elab.lean:9240–9265`), `#sim`
(`Elab.lean:9308–9322`), `#simChecked` (`Sparkle/Compiler/SimChecked.lean:76–87`); compiled by
`Sparkle.Core.JIT.compile` (`Sparkle/Core/JIT.lean:186–213`: `cc -shared -fPIC -O2 -std=gnu11
-fvisibility=hidden -I <dir> [-Wl,-rpath,<libc dir>] -o .lake/build/jit_cache/<hash>.so <file>`); loaded by
`c_src/sparkle_jit.c:170–180` (`dlopen`, then `dlsym(lib, "jit_vtable")` — ONE fixed exported symbol, no
generated name is ever passed to `dlsym`). The cache file name is a hash of the C text, not a name.

| conversion (file:line) | input → output | injective on `ofDecl`'s image? | on wire / instance names? | collision example; reachable?; effect |
|---|---|---|---|---|
| `Backend.Verilog.sanitizeName` (`Sparkle/Backend/Verilog.lean:32`): identity if all chars are letters / digits / `_` / `$`; else `.`,`-`,space→`_`, `'`→`_prime`, `#` deleted | module names (`:452`), instance targets and instance names (`:395`), ports, wires | yes: identity (`Tools.ShippingModuleName.sanitizeName_encode`, proved) | yes: identity on allocated names (`freshName_clean`) | `a.b` / `a_b`, `a#` / `a` — only for module names made by hand (`validateDesignNames` refuses them: `Sparkle/IR/ModuleNameCheck.lean:17`). Not reachable from declarations since b7dc0ec4. External / primitive module names are user strings in no tagged namespace (open, recorded in verification-h-fix.md) |
| `Backend.CSim.sanitizeName` (`Sparkle/Backend/CSim.lean:74`): the same text | `struct <m>`, `sparkle_<m>_{reset,eval,tick,eval_tick}`, members, instance fields | yes: identity | yes: identity | as a FUNCTION no collision on compiler names. The identifiers BUILT from it collide or break: J1–J4 below |
| `CSim` member qualification, `isTokChar` (`CSim.lean:1996–1997`; used by `qualifyWith` `:1999–2036`): a token is a maximal run of letters / digits / `_` — `$` ends a token | every body line; a token that is a member name gets `self->` | n/a | **no `$` name is ever recognised as a member** | **J1**: instance `_tmp_inst_Sp$D$x_0` → lines `_tmp_inst_Sp$D$x_0._gen_x = self->_gen_x;`, `sparkle_Sp$D$x_eval(&_tmp_inst_Sp$D$x_0);` without `self->` → C error "undeclared". Reachable: any parent of a tagged child. Error at C compile |
| `CSim` function names (`CSim.lean:2070, 2087, 2103, 2161`): `sparkle_<m>_reset`, `_eval`, `_tick`, `_eval_tick` | module name + verb suffix | **no** (as a map from (module, verb)) | — | **J2**: modules `X` and `X_eval` both define `sparkle_X_eval_tick` (eval_tick of `X`, tick of `X_eval`). Reachable: two plain declarations `fk`, `fk_eval` in one design. Both are `static` in one translation unit with different parameter types → C error |
| `CSim` struct tag (`CSim.lean:1943`): `struct <m>` | module name | yes | — | **J3**: a module named like a C keyword that is not an SV keyword (`volatile`, `double`, `float`, `char`, `long`, `short`, `auto`, `goto`, `switch`, `sizeof`, `inline`, `restrict`, `register`): `struct volatile {` → C error. Reachable: a root-level declaration of that name (plain form: no namespace). Error |
| `CSim` JIT trampolines (`CSim.lean:2692–2702`): fixed names `sparkle_jit_{create,destroy,reset,eval,tick,eval_tick,…}` | — | — | — | **J4**: a module named `jit` defines `sparkle_jit_reset(struct jit*)`, the trampoline `sparkle_jit_reset(void*)` → C error. Reachable: a root-level declaration `jit`. Error |
| `CSim` register next value (`CSim.lean:1450`): `<reg>_next` | register output name | — | not in general | a register `_gen_r` next to a wire `_gen_r_next` → duplicate struct member (C error) or, in `eval_tick`, a local shadowing a member. Whether the compiler ever names a register `_gen_<binder>` was NOT determined by reading; row `regnext` probes it |
| `CSim` instance field (`CSim.lean:1601, 2555`; `CudaIntra.lean:116–119`): `<inst>_inst` if the instance name equals the module name | instance name | — | yes for compiler output | never fires on compiler output (`_tmp_inst_<m>_<n>` ≠ `<m>`); only for parsed SV |
| `CSim.hoistWideForC` (`CSim.lean:2193`): `_wide_hoist_<c>` | fresh wires | — | disjoint from `_gen_` / `_tmp_` / `out` | none seen |
| `Backend.CudaSim` (`CudaSim.lean:73, 77, 120, 153, 285`), `CudaIntra` (`:117–118, 240–325`) | reuse `CSim.sanitizeName`: `struct <m>`, `sparkle_<m>_eval_tick`, `offsetof(struct <top>, <field>)` | identity | identity | J2 / J3 apply by the same text; `$` in `offsetof` field names untested. `nvcc` is not on this machine: UNVERIFIED |
| `Backend.Smt.sym` (`Sparkle/Backend/Smt.lean:34`): `\|<sanitizeName name>_c<frame>\|` | wire names per frame | module names are not symbols | yes: `(name, frame)` is read back from the last `_c<digits>` | none |
| `IR.Builder.sanitizeName` (`Sparkle/IR/Builder.lean:227`) then `NameHints.clean` (`NameHints.lean:24`) | wire HINTS (binder names, `inst_<module>`) | n/a | not injective by design (`x.y` / `x_y`, `é` / `è` → `_`) | harmless: the allocator searches an unused name (`freshName_spec`, proved). Row `unibind` exercises two non-ASCII binders |
| `simLeanIdent` on the LAST component (`Elab.lean:9296–9297, 9317–9319`; `SimChecked.lean:64–65, 82–84`) | declaration → Lean namespace `<ns>.Sim` / `<ns>.SimChecked` and FILE names `.lake/build/gen/sim/<ns>_jit.c`, `<ns>.sv` (`#simChecked`: `.lake/build/gen/simchecked/`) | **no**: not a function of the module name at all | — | **J5**: `A.f` / `B.f`; `fé` / `fè` (both `f_`). Same environment: the second command fails ("already declared") AFTER overwriting the files. Different files: SILENT overwrite; `load` compiles the file at run time, so the earlier simulator loads the later design. Reachable; the ten `#sim` declarations found under `IP Examples Tests` have ten different last components. A digit-initial last component (`1bad`) is refused by the parser (`namespace 1bad.Sim`), after the files were written |
| `Verilator.of` (`Sparkle/Core/SimVerilator.lean:65, 134`) | top name → C++ class `V<top>`, `V<top>.h`, `V<top>.so` | identity (injective) but not what Verilator emits for `$` | — | 2b: predicted build error for a tagged top |
| `#writeDesign` JIT path (`Elab.lean:9262–9263`): `cppPath.replace "_cppsim.h" "_jit.c"` | user path → user path | n/a | n/a | not a name issue: a `cppPath` without `_cppsim.h` makes the JIT file path EQUAL to the C file path — the second write replaces the first, silently (the JIT text contains the class text) |
| `Tools/SVParser/SimMacro.lean:52, 74, 80` (`sim!`) | PARSED module name → namespace and `.lake/build/gen/sim/<ns>_jit.c` | not `ofDecl` | — | shares the directory and the scheme of `#sim`: a parsed module `f` and a declaration `…f` overwrite each other (J5's shape) |
| `Tools/SVParser/VerifyEmit.lean:274`, `DslEmit.lean:414, 492` | `declName.toString.replace "." "_"` → THEOREM names | n/a (not module names) | — | `A.b_c` / `A_b.c` → one theorem name; "already declared" error. Not on the compiler route |
| `Sparkle/Core/TimerOracle.lean:161` | `regName.replace "." "_"` | n/a | lookup key for a user-supplied register name | not examined further |

Hand-written couplings to generated names (all PLAIN today): `fpga/tangNano20k/*_top.v` (five wrappers),
`verilator/rv32i_soc_wrapper.sv:35`, `verilator/tb_cppsim.cpp:52`.

## 3. Findings

**J1 — C backend: a parent of a tagged module does not compile (PREDICTED).** `CSim.lean:1996`:
`isTokChar c := c.isAlphanum || c == '_'`. The instance field is declared `struct Sp$D$x _tmp_inst_Sp$D$x_0;`
(member name found by `extractDeclName`, with its `$`), but in the eval / tick / reset bodies the scanner
sees the tokens `_tmp_inst_Sp`, `D`, `x_0`, none of which is a member, and emits them bare. Supported path:
`#sim`, `#simChecked`, `#writeDesign`, `#writeCppSimDesign`; the failure appears when the C is compiled
(`JIT.compile` throws "JIT compilation failed"). Reachable from: a `private` `@[hardware_module]`; a
declaration named with a keyword or a leading digit; a lower-case namespace (`a.b`); a non-ASCII name; a
declaration named like a memory module. Before b7dc0ec4 the private case had no `$`
(`_private_IP_Crypto_AESHW_0_…`) and did not have this problem — the tagged encoding introduced it. In the
tree no `private` declaration carries `@[hardware_module]` (grep), and the two private AES declarations are
TOPS (a tagged top with plain children is predicted to compile), so no existing test is predicted to break.
Rows: `priv`, `kw`, `dig`, `alias`, `uni`, `mem` (`csim-cc`, `csim-ids unqualified-inst-lines`), and
`simcmd-priv` (the real `#sim`).
Smallest fix (NOT made): `isTokChar c := c.isAlphanum || c == '_' || c == '$'` — one line; the C backend emits
`$` only inside identifiers.

**J2 — C function names `sparkle_<m>_<verb>` are ambiguous (PREDICTED).** `fk` and `fk_eval` under one
parent: `sparkle_…_fk_eval_tick` twice. Not about tags (both names are plain). C compile error. Row `cfn`.
Smallest fix: put the verb first with codes no one of which is a prefix of another including the separator
(`sparkle_e_<m>`, `sparkle_t_<m>`, `sparkle_et_<m>`, `sparkle_r_<m>`), which also separates them from the
`sparkle_jit_` trampolines (J4).

**J3 — a module named like a C keyword (PREDICTED).** `struct volatile`. Row `ckw`. Smallest fix: a fixed
prefix on the struct tag (`struct sparkle_m_<m>`).

**J4 — a module named `jit` (PREDICTED).** Row `cjit`. Fixed by J2's fix.

**J5 — `#sim` / `#simChecked` / `sim!` output files by last component (known; SILENT across files).**
Rows `simdup`, `simcmd-uni1/uni2`, `simcmd-dig`. Smallest fix: derive the file name from
`ModuleName.ofDecl declName` (injective), keep the Lean namespace.

**Verilator shim with a tagged top (PREDICTED, less certain).** `Verilator.of` writes `#include "V<top>.h"`.
Rows `privself` / `kwself` / `digself` `verilator-cc`: `literal-top-header F`. Smallest fix: pass an explicit
`--prefix` and use it for the class and the include.

J1–J4 are errors (nothing wrong is simulated); J5 is the only silent one. None was fixed: the compiler is
untouched.

## 4. The examples

`scripts/shipping-coverage/tagged_names_sim.lean` (one Lean process; imports
`Tests.Compiler.CacheCoherenceProbe`), driver `scripts/shipping-coverage/tagged_names_sim.sh`, outputs under
`.lake/build/gen/tagged-names/`. Every row is a Lean declaration compiled by the real entry; the text is the
REAL command `#writeVerilogDesign`; the C is `CSim.toCJIT (Optimize.optimizeDesign design)` (the recipe of
`#sim`, `Elab.lean:9313–9315`).

| row | top declaration | what it has |
|---|---|---|
| `priv` | `TaggedNamesSimZZ.privTop` | instantiates `private def privKid` (`Sp$D$__private$…$privKid`) |
| `privself` | `privKid` | the private declaration as the top |
| `kw` | `kwTop` | instantiates `«module»` (`Sp$D$module`) and `«always_ff»` (`Sp$D$always__ff`) |
| `kwself` | `«module»` | the keyword declaration as the top |
| `dig` | `digTop` | instantiates `«1bad»` (`Sp$D$1bad`) |
| `digself` | `«1bad»` | as the top |
| `alias` | `aliasTop` | `a.b` (tagged) + `a_b` (plain `TaggedNamesSimZZ_a_b`) + `Al.b` (plain `TaggedNamesSimZZ_Al_b`) + `Al_b` (tagged): four children adding 1, 2, 4, 8 |
| `uni` | `uniTop` | `«café»` (`…$caf_233_`), `«加算»` |
| `unibind` | `uniBindTop` | child with BINDERS `«入»`, `«力»` (wire names, plain module name) |
| `mem` | `CacheCoherenceProbe.mmTop` | a memory (`SparkleMem_combo_4_8`) next to the declaration `SparkleMem_combo_4_8` (`Sp$D$SparkleMem__combo__4__8`) |
| `cfn` | `cfnTop` | `fk` + `fk_eval` (J2) |
| `ckw` | `ckwTop` | root declaration `volatile` (J3) |
| `cjit` | `cjitTop` | root declaration `jit` (J4) |
| `regnext` | `regNext` | `let r_next := x + 1; let r := Signal.register 0 r_next` (probe) |

`tagged_names_simcmd.lean`: the real `#sim` on `tnzPrivKid` (private, top), `tnzPrivTop` (parent of it),
`«tnzé»`, `«tnzè»`, `«module»`, `«1bad»`. `tagged_names_simdup_a.lean` / `_b.lean`: `#sim DupA.tnzDup`, then,
in a second process, `#sim DupB.tnzDup`.

Line format: `TAGGEDNAMES <example> <tool>: exit=<n> <facts>`; `UNAVAILABLE` for a tool not on PATH;
`NOT RUN — <reason>` when a row has no input for the tool. The script exits 0 always and ends with a summary
(rows, non-zero exits, trace mismatches, module-set mismatches, C identifier duplicates, unqualified
instance references).

### How to run

```
lake build Tests.Compiler.CacheCoherenceProbe        # once, serially, under cgrun
scripts/shipping-coverage/cgrun.sh -n tagged -m 3G -t 1800 -- scripts/shipping-coverage/tagged_names_sim.sh
```

Environment: `SPARKLE_TAGGEDNAMES_NA` / `_NB` (cycles of the two run phases, default 64 / 24),
`SPARKLE_TAGGEDNAMES_LEAN_TIMEOUT` (seconds per Lean process, default 600). The script starts four Lean
processes, one after another. It writes `tnz*`, `module*`, `1bad*` under `.lake/build/gen/sim/` (the `#sim`
rows) and removes them at the end.

## 5. PREDICTED outcomes (nothing run)

Lean step: every row is predicted to compile, with two reservations — a `private` declaration as a CHILD
(`priv`) and non-ASCII binders (`unibind`: `Elab.lean:7916` looks an input up by `"_gen_" ++
binderName.toString`, the allocator stores the cleaned name) were not followed to the end by reading. A row
whose Lean step fails prints `NOT RUN` for every tool.

| row | iverilog | yosys | verilator (lint) | verilator-cc | csim-ids | csim-cc | csim-run |
|---|---|---|---|---|---|---|---|
| `priv` | exit 0, `command==source T` | exit 0, `modules==expected T` (2) | exit 0 | exit 0, `literal-top-header T`, child header with `__024` | `unqualified-inst-lines` > 0, no dups | **exit ≠ 0 (J1)** | exit ≠ 0, `c==source -` |
| `privself` | 0, T | 0, T (1) | 0 | 0, **`literal-top-header F`** | 0 unqualified | 0 | 0, `c==source T` |
| `kw` | 0, T | 0, T (3) | 0 | 0, T | > 0 | **≠ 0 (J1)** | ≠ 0 |
| `kwself` | 0, T | 0, T (1) | 0 | 0, **F** | 0 | 0 | 0, T |
| `dig` | 0, T | 0, T (2) | 0 | 0, T | > 0 | **≠ 0 (J1)** | ≠ 0 |
| `digself` | 0, T | 0, T (1) | 0 | 0, **F** | 0 | 0 | 0, T |
| `alias` | 0, T | 0, T (5 distinct) | 0 | 0, T | > 0 (two tagged children) | **≠ 0 (J1)** | ≠ 0 |
| `uni` | 0, T | 0, T (3) | 0 | 0, T | > 0 | **≠ 0 (J1)** | ≠ 0 |
| `unibind` | 0, T (if the Lean step passes) | 0, T (2) | 0 | 0, T | 0 | 0 | 0, T |
| `mem` | 0, T (as `module_name_sim`) | 0, T (4: top, `memKid`, memory module, tagged declaration) — `check -assert` is new relative to the earlier partial run | 0 (earlier partial run: 0) | 0, T | > 0 | **≠ 0 (J1)** | ≠ 0 |
| `cfn` | 0, T | 0, T (3) | 0 | 0, T | **`dup-funcs=[sparkle_TaggedNamesSimZZ_fk_eval_tick]`** | **≠ 0 (J2)** | ≠ 0 |
| `ckw` | 0, T | 0, T (2) | 0 | 0, T | no dups | **≠ 0 (J3)** | ≠ 0 |
| `cjit` | 0, T | 0, T (2) | 0 | 0, T | **`dup-funcs`: `sparkle_jit_reset`, `_eval`, `_tick`, `_eval_tick`** | **≠ 0 (J4)** | ≠ 0 |
| `regnext` | 0, T | 0, T (1) | 0 | 0, T | not predicted | not predicted | not predicted |

| `#sim` row | predicted |
|---|---|
| `simcmd-privself` | `lean-errors=0`, file written, `csim-cc exit=0` |
| `simcmd-priv` | `lean-errors=0` (the command succeeds), file written, **`csim-cc exit≠0` (J1)** — `load` would throw at run time |
| `simcmd-uni1` | `lean-errors=0` |
| `simcmd-uni2` | `lean-errors>0` ("already declared" in `tnz_.Sim`), the file now holds the SECOND design (J5) |
| `simcmd-kw` | not predicted (`namespace module.Sim`: whether the parser takes `module.Sim` as one identifier) |
| `simcmd-dig` | `lean-errors>0` (parse error at `namespace 1bad.Sim`), file `1bad_jit.c` written, `csim-cc exit=0` |
| `simdup` | `exit=0/0`, `overwritten-without-error=T`, top struct `DupA_tnzDup` then `DupB_tnzDup` (J5) |
| `simcmd lean` | process exit 1 (expected: two cases are refused) |

Confidence: the SV-tool rows repeat, on real private / keyword / digit / non-ASCII declarations, what the
earlier partial run saw for the `#ccp.k` names (exit 0); the tagged-TOP rows under Verilator and yosys are
new. J1–J4 follow from the emitter's text; they are still predictions until gcc says so.

## 6. What stays unverified

* Vendor FPGA flows (`fpga/tangNano20k/*.sh`: `synth_gowin`, nextpnr-himbaechel, gowin_pack, openFPGALoader,
  the board): not run, need tools / hardware outside this check. The driver's yosys row is the generic
  front end (`read_verilog`, `hierarchy`, `proc`, `opt`, `check`), not `synth_gowin`.
* `hw/synth/synth.ys`: usage comments for inputs that are not in the tree; `techmap` / `abc` not run.
* CUDA backends (`CudaSim`, `CudaIntra`): `nvcc` is not on this machine. J2 / J3 are predicted for them by
  the shared text; `$` in their device code is unexamined.
* `Verilator.of` end to end (`--cc --build`, load the `.so`): the driver stops at `--cc` (no C++ build) and
  reports the header names; the shim itself is private to `SimVerilator.lean` and is not emitted here.
* `JIT.compileAndLoad` from Lean (`dlopen` through the FFI): the driver compiles with the same flags and
  runs the same vtable from a C `main`; it does not go through `c_src/sparkle_jit.c`.
* `bench/xiangshan` yosys / co-simulation flows: parsed names only; not run here.
* Any simulator or synthesiser not listed (Icarus is the only event simulator; no commercial tool).

## 7. Not determined by reading

* Whether a `private` `@[hardware_module]` is accepted as a CHILD by the sub-module route (the AES
  precedents are tops) — row `priv` / `simcmd-priv`.
* Whether a register can be named `_gen_<binder>` (so that `<reg>_next` can meet a wire) — row `regnext`.
* Whether a structure-result FIELD name can become a bare port name that is a C or SV keyword (ports are
  otherwise `_gen_…`, `out`, `clk`, `rst`): the result-port naming (`Elab.lean:1898–1965`) was not followed.
* Verilator's default prefix for a top containing `$` (`V<encoded top>` is assumed).
* Whether yosys 0.69 still prints `=== <module> ===` in `stat` (the module-set comparison depends on it; a
  format change shows as `modules==expected F` with an empty `yosys=[]`).
* `Lean` main-module name in a private name when a file is elaborated by `lake env lean <file>` (`_stdin`
  assumed in the examples of this document; the driver prints the real name).
* Lowered-SV designs (`Tools/SVParser`) through the C backend: module names there are parsed strings, may
  contain `$` from the source, and J1 would apply to them equally; not examined (they pass co-simulation in
  CI, so `$` instance names are presumably absent from that corpus).

## Integrator's run record (2026-10-14) — MEASURED

Run `tagged` on poc df990315 + these files: `cgrun.sh -n tagged -m 3G -t 2400 -- scripts/shipping-coverage/tagged_names_sim.sh`
(exit 0, peak 0.41 GB; outputs `.lake/build/gen/tagged-names/`, driver output `~/sparkle-work/tagged.out`).
Tools: iverilog 13.0, Yosys 0.69, Verilator 5.052, gcc 15.3.0. The driver's Lean step: exit 0.

SystemVerilog side, all rows that ran (`alias`, `cfn`, `cjit`, `ckw`, `dig`, `digself`, `kw`, `kwself`,
`mem`, `priv`, …): iverilog `command==source T`, 0 x-cycles; yosys exit 0 with `modules==expected T`
(the tagged names are distinct modules: e.g. `Sp$D$TaggedNamesSimZZ$a$b` next to `TaggedNamesSimZZ_a_b`);
Verilator lint exit 0, 0 warnings. Verilator `--cc`: exit 0 except `ckw` (a module named `volatile`);
for a TAGGED TOP the generated header is not `V<top>.h` (`literal-top-header F`: `$` is encoded as
`__024`), so the repository's `Verilator.of` shim would not find it (not run end to end).

C backend (`CSim.toCJIT`, compiled with the repository's own flags), MEASURED:
* **J1 CONFIRMED** — a parent that instantiates a tagged module does not compile: rows `priv`, `kw`,
  `dig`, `alias`, `mem`: `csim-cc exit=1`, `unqualified-inst-lines` 7–14. gcc:
  "'_tmp_inst_Sp$D$__private$…$privKid_1' undeclared (first use in this function)" in the generated
  `…_reset` (the instance member is referenced without `self->`). A tagged module as the TOP is fine
  (`privself`-style rows `kwself`, `digself`: `csim-cc exit=0`, `c==source T`).
  This is a REGRESSION of commit b7dc0ec4 (injective module names) for `private` children in the C
  simulation / JIT path: before it a private child's module name had no `$`. For keyword / digit / alias
  names it is a new failure mode (they were refused before). A compile ERROR, not a silent wrong result.
* **J2 CONFIRMED** (older than the tags) — row `cfn`: "conflicting types for
  'sparkle_TaggedNamesSimZZ_fk_eval_tick'" (modules `fk` and `fk_eval`).
* **J3 CONFIRMED** (older) — row `ckw`: `struct volatile {` → "expected '{' before 'volatile'".
* **J4 CONFIRMED** (older) — row `cjit`: duplicate `sparkle_jit_eval` / `_tick` / `_reset` / `_eval_tick`.
Not read by the integrator in this pass: the `#sim` command rows (`simcmd-*`, `simdup`: J5), `regnext`,
the non-ASCII rows — their lines are in `~/sparkle-work/tagged.out`.
NOT fixed: every fix is a change of the C emitter (compiler backend) and awaits a ruling. Smallest fix for
J1 (by the worker's reading): `isTokChar c := c.isAlphanum || c == '_' || c == '$'` at
`Sparkle/Backend/CSim.lean` 1996.
