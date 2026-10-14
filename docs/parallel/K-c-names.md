# Output paths, generated Lean names and C identifiers (worker K, branch `fix/c-names`) — WRITTEN, NOT BUILT/RUN

Reviewer's rulings of 2026-10-14 (second message), items 1–2: J1 integrated first with a small REAL JIT path;
J2–J5 fixed in independent commits, J5 first (paths and generated Lean names together, from the qualified
declaration identity), J2–J4 through one shared encoding of C identifiers.

Base: `poc/roundtrip-proof` 80745d94. Nothing in this document was built or run: no `lean`, `lake`, `gcc`,
`iverilog`, `yosys`, `verilator` was started. Every outcome is a PREDICTION from reading and is labelled so.

| unit | commit | what |
|---|---|---|
| base | 1a2e123b | the J1 line as being integrated (`isTokChar … \|\| c == '$'`, comment naming `$`) — nothing else |
| A | a244dd32 | test only: a private child through the real JIT path (Lean FFI) |
| B | 55613270 | J5: paths and generated Lean names from the qualified declaration |
| C | 24cd50c4 | J2–J4: one injective encoding of the module-derived C identifiers |
| D | the commit after C | this document |

Each of B and C can be reverted alone (C does not touch the files of B except the driver script and its Lean
file, where the hunks are disjoint). J2–J4 are ONE commit on purpose: they are one function (`cIdent`) applied
at the same emission sites; split in three, every intermediate tree would have the struct tag in one scheme
and the functions in another, and each consumer (tests, cosim drivers, fixture) would be edited twice.

NOT claimed anywhere below: "all backends supported". The CUDA emitters (no `nvcc` here) and the
`Verilator.of` shim for a tagged TOP stay UNVERIFIED (§6).

## 1. Unit A — the real JIT path, one small case (test only)

`Tests/Compiler/TaggedJitE2ETest.lean`. A parent `tagJitE2ETop` with a `private` `@[hardware_module]` child
(tagged module name, so the instance member is `_tmp_inst_Sp$D$…`).

What it drives, exactly:
* elaboration time: the real command `#sim tagJitE2ETop` (writes the C text);
* run time: `tagJitE2ETop.Sim.load` = `Sparkle.Core.JIT.JIT.compileAndLoad` → `JIT.compile` (`cc -shared -fPIC
  -O2 -std=gnu11 -fvisibility=hidden …`, `Sparkle/Core/JIT.lean:186`) → `JIT.load` = the extern
  `sparkle_jit_load` of `c_src/sparkle_jit.c:162` (`dlmopen` / `dlopen`, `dlsym "jit_vtable"`, `create`);
* 16 cycles through the generated typed wrapper (`Simulator.step` = `JIT.setInput` + `JIT.evalTick`,
  `Simulator.read` = `JIT.getOutput`), then 16 cycles through the raw FFI on the same handle (`JIT.setInput`,
  `JIT.eval`, `JIT.getOutput`, `JIT.tick`); every cycle compared with the SOURCE function evaluated in Lean;
* it also asserts that the C text it runs contains `self->_tmp_inst_Sp$D$` (the tagged member, qualified).

This is DISTINCT from the driver's rows (`tagged_names_sim.sh`, `csim-cc` / `csim-run`): those compile with
the same flags but run the vtable from a C `main`; they never go through `c_src/sparkle_jit.c` and never call
`eval_tick`. The typed wrapper here calls the FUSED function (`eval_tick`), whose instance-call rewriting
(`CSim.lean`, `evalTickEvalBody`) is not exercised by any driver row.

Needs: compiled code (the FFI symbols are in the test executable; `#eval` does not have them) and `cc` on
PATH at run time. Existing JIT tests in the suite (`Tests/SVParser/TestVerilogCoSim.lean`) catch EVERY
exception and report a passing "SKIP" row — a compile failure would pass there. This test skips only when
`cc --version` cannot be started; everything else is a failed row or an exception.

Suite: suitable, in the pattern of `TestVerilogCoSim` (an `IO TestSeq` called from `main`). To add to
`Tests/AllTests.lean` (not edited by me):

```
import Tests.Compiler.TaggedJitE2ETest
…
  let taggedJitTests ← Tests.Compiler.TaggedJitE2ETest.tests
  let allTests := allTests ++ taggedJitTests
```

Smallest EXISTING test through the real loader, for reference: `Tests/IP/Net/CRC32JITTest.lean` (exe
`crc32-jit-test`, `lakefile.lean:1385`; needs `cc`; not in the suite) and the three rows of
`TestVerilogCoSim` (in the suite; parsed SV, not a declaration).

PREDICTED: 2 rows pass (`tagged-member-in-C=true`, `mismatches=0`). Assumptions I could not check by
reading: the input field is named `_gen_x` and the output `out` (the pattern of `CRC32JITTest`); a
combinational top has no `rst` input, so slot 0 is `x` (if the module had `rst`, BOTH phases would be off —
`#sim`'s numbering skips `rst`, the JIT's does not: the known defect of `Tests/Compiler/SimIndexTest.lean`).

## 2. Unit B — J5: `#sim` / `#simChecked` / `sim!` / `#writeDesign`

### 2a. Diff summary

New file `Sparkle/Compiler/SimNames.lean` (pure functions, 131 lines):

| function | value |
|---|---|
| `declFileKey n` | `ModuleName.ofDecl n`, unchanged up to 180 characters; longer: first 120 characters + `-h<hash>` |
| `declNamespace n` | the user-facing name, each component between `«` and `»` (`A.f` → `«A».«f»`); a name with a numeric / empty component or a `»` → `«<ofDecl n>»` |
| `declIsPrivate n`, `withVisibility` | a private declaration gets `private` in front of every generated `def` / `structure` / `instance` |
| `svFileKey name cText` (for `sim!`) | module name (or `Sp$S$<encStr>` when not plain) + `-` + hash of the C text |
| `svNamespace name` (for `sim!`) | the module name as ONE component, `«…»` when not a plain identifier |
| `writeDesignPaths cppPath` | `(C path, JIT path)`, never equal |

`Sparkle/Compiler/Elab.lean` (`#sim`, `:9316–9458`) and `Sparkle/Compiler/SimChecked.lean` (`:72–214`):
* the stem of the two files is `declFileKey declName` (was: last component, sanitised);
* the wrappers are elaborated under the ABSOLUTE namespace `<declNamespace>.Sim` / `.SimChecked`: the
  current namespace is set to the root for the duration (`modifyScope`), the scopes are restored in a
  `finally` (also when a generated command fails — before, a failure left `namespace <ns>.Sim` open);
* the body is otherwise unchanged; it is re-indented under `try`, so `git diff -w` shows the real change
  (`elabSimStr` → `emit`, the six lines before the `try`, the `finally`).

`Sparkle/Compiler/Elab.lean:9258–9268` (`writeDesignCore`): the two C paths come from `writeDesignPaths`.
`Tools/SVParser/SimMacro.lean:81–88, 108, 190`: `sim!` uses `svFileKey` / `svNamespace`.

### 2b. Injectivity through the file-name step — what is relied on, what is not solved

* RELIED ON: `ofDecl` is injective on ALL `Lean.Name`s (`Tools.ShippingModuleName.ofDecl_injective`,
  proved). The stem is `ofDecl n` itself for names up to 180 characters, so two such declarations have two
  stems; the suffixes (`_jit.c`, `.sv`) differ in the extension, so the four paths of two declarations are
  pairwise distinct.
* File-name safety of the alphabet (letters, digits, `_`, `$`): no `/`, no `.`, no `-`, no space. `$` is an
  ordinary character in a POSIX file name; the paths reach `cc` and `verilator` as process ARGUMENTS
  (`IO.Process.output`, no shell) and Lean as a string literal (no escape needed for these characters). A
  shell script that names such a file must quote it (the driver does).
* Length: a stem longer than 180 characters is cut to 120 and gets `-h<64-bit hash of the whole stem>`
  (file name ≤ 148 + suffix). Such a stem contains `-`, an uncut one does not: the two forms are disjoint.
  Two LONG names are kept apart only up to the hash — NOT injective in the strict sense, stated.
  Why not simply fail: before, any qualified name gave a short file name (last component); refusing long
  names would turn a working input into an error.
* `sim!` stems always contain `-` followed by decimal digits; cut declaration stems end in `-h` + digits;
  uncut ones have no `-`: the three forms are pairwise disjoint, so a parsed design never shares a file with
  a declaration (they share the directory `.lake/build/gen/sim/`).
* NOT SOLVED: (1) a case-insensitive file system (`Foo.bar` / `FOO.bar` → `Foo_bar` / `FOO_bar`): a stem
  that is injective after case folding would have to mark upper-case letters and so change every existing
  file name; not done. (2) Two declarations with the SAME qualified name in two files never imported together
  (one identity → one path; the second run replaces the first — only a content hash would separate them, and
  hand-written paths in drivers would no longer be writable). (3) Private declarations of two files
  elaborated OUTSIDE lake (`lake env lean a.lean`, `… b.lean`): Lean itself gives both the main-module name
  of a stand-alone file, so their private names — and stems — are equal. (4) Hash collisions in the two
  hashed forms.

### 2c. Generated Lean names

Namespace = the qualified user-facing name + `Sim` / `SimChecked`, absolute. Injective on public
declarations whose components can be written between `«»` (every name a user can write in source). Private
declarations of two files have the same user-facing name; their wrappers are generated `private`, i.e. under
the private prefix of their own module, so they are different constants. Residue: the instances that
`deriving Repr, BEq, Inhabited` creates for a private structure — whether Lean makes those private was not
determined by reading (if not, two files with a private declaration of one name clash only when both are
IMPORTED into a third file: a loud import error).
The fallback `«<ofDecl n>»` (numeric components — machine-made names) can in principle equal a user
declaration literally named `«Sp$D$…»`; in one environment that is an "already declared" error, not silent.

### 2d. Compatibility (grep over `Tests IP Examples scripts fpga docs Sparkle Tools`)

| referenced thing | before | now | in-tree references |
|---|---|---|---|
| namespace, command run INSIDE the declaration's namespace | `<ns>.<last>.Sim` | the same constant | all eight `#sim` users: `Tests/IP/Crypto/Keccak256SpongeJITTest.lean:47`, `Tests/IP/Control/ControlJITTest.lean:60,71,76,87`, `Tests/IP/Net/{UsbWebServer:95,IPv4:39,MemcachedServer:47,CRC32:44}JITTest.lean`, `Tests/Synthesis/TopLevelSimJITTest.lean:42` — NO edit needed |
| namespace, command run OUTSIDE it | `<current ns>.<last>.Sim` | `<declaration>.Sim` | `Tests/Compiler/SimIndexTest.lean:118–119` (`#check @softRst.SimChecked.…`) — UPDATED to the qualified name |
| namespace, last component not ASCII alphanumeric | sanitised (`tnz_`) | the real component (`«tnzé»`) | driver only (`tagged_names_simcmd.lean`) — comments updated |
| file stem, root-level plain name `f` | `f` | `f` (unchanged: `ofDecl` of a root plain name is the name) | `docs/tutorial/md/Ch08b_Simulation.md:165,233,403–404` (`counter8`) stay true |
| file stem, any other declaration | last component | `ofDecl` (e.g. `Sparkle_Tests_IP_Net_CRC32JITTest_crc32Top`) | the eight users load through `…Sim.load` / `jitCppPath`, not a literal — no edit |
| literal paths `.lake/build/gen/sim/<x>Top_jit.c` | — | — | 27 files `Tests/Drivers/*JIT*.lean` (`ExpJIT.lean:11`, `MemJITTest.lean:12,28`, …): the `#sim` commands that write these files are NOT in the tree (no declaration named `expTop`, `mem8Top`, … found by grep). NOT updated; if those declarations are root-level plain names the paths are unchanged, otherwise each needs `<ofDecl>` — could not be determined |
| `sim!` namespace, plain module name | `<name>.Sim` | the same | no `sim!` in any `.lean` of the tree (docs only: `docs/Tutorial.md:256,663,692`, `Ch05_Verilog.md:267`) |
| `sim!` namespace, non-plain name (`a$b`) | `a_b.Sim` | `«a$b».Sim` | none |
| `sim!` file | `<name>_jit.c` | `<name>-<hash>_jit.c` | none (the docs use `…Sim.load` / `jitCppPath`) |
| `#writeDesign`, C path with `_cppsim.h` | C at the path, JIT at `…_jit.c` | the same | all 18 uses in the tree |
| `#writeDesign`, C path WITHOUT `_cppsim.h` | the JIT text REPLACED the C text at that one path | the JIT text at that path (as before), the C text at `<path>_cppsim.h` | none in the tree |

Disjointness of old and new stems is not needed for correctness (old files are stale artifacts, nothing reads
them through the new names), but for the record: a root-level plain name keeps its stem, and no OTHER
declaration can now get that stem, because the new map is injective and that stem is already the image of the
root name.

### 2e. Regression

`Tests/Compiler/SimNamesTest.lean` (elaboration time, no external tool; throws on failure; suitable for the
suite — to add: `import Tests.Compiler.SimNamesTest` in `Tests/AllTests.lean`):

| # | case | how | PREDICTED |
|---|---|---|---|
| i | `SimNamesTestA.snDup` / `SimNamesTestB.snDup`, one environment | the real `#sim` twice; then paths differ, each file holds its own module name and not the other's (JIT C and `.sv`) | pass (before: the second command failed after overwriting) |
| iii | `«snUé»` / `«snUè»` | the real `#sim` twice; paths differ; files hold `Sp$D$snU_233_` / `…_232_` | pass |
| iv (same environment) | `#sim SimNamesTestA.snDup` AGAIN | elaborated from text; DOCUMENTED behaviour asserted: an error is reported ("already declared"), no file changes content, the current namespace is what it was | pass. Lower confidence on "content unchanged": it needs the second synthesis in one process to print the same text (not determined by reading whether the compiler's caches can change a wire name on a second run) |
| v | `#writeDesign` with `…/wd.c` | the real command; `wd.c` holds the JIT text, `wd.c_cppsim.h` the C text | pass |
| — | 41 `#guard`s on `SimNames` | stems, namespaces, long names, private names, `writeDesignPaths`, `sim!` stems | pass. The exact strings (`Sp$D$snU_233_`, `«A».«f»`) are computed by hand from `ModuleName.lean` |

Driver rows (`scripts/shipping-coverage/tagged_names_sim.sh`; they need the script, not the suite):

| row | PREDICTED |
|---|---|
| ii `simdup` (two files, two processes) | `exit=0/0`, `A=…/DupA_tnzDup_jit.c after-A=<h1>(…DupA_tnzDup) after-B=<h1>`, `B=…/DupB_tnzDup_jit.c after-B=<h2>`, `old-shared-path=absent`, `overwritten-without-error=F`, `each-has-its-own-file=T`, `lean-errors=0/0` (measured before: `overwritten-without-error=T`) |
| iv `simrerun` (same file again, fresh process) | `exit=0`, `same-path-same-content=T`, `B-untouched=T`, `lean-errors=0` |
| `simcmd-privself` | `lean-errors=0`, `file=written(Sp$D$__private$<main module>$_0$tnzPrivKid_jit.c)`, `csim-cc exit=0` — the only row with PRIVATE wrappers; if `private structure … deriving` or `private instance` is refused, it shows here |
| `simcmd-priv` | `lean-errors=0`, `file=written(tnzPrivTop_jit.c)`, `csim-cc exit=0` |
| `simcmd-uni1`, `-uni2` | `lean-errors=0` both (before: `uni2` "already declared"), files `Sp$D$tnz_233__jit.c`, `Sp$D$tnz_232__jit.c` |
| `simcmd-kw` | `lean-errors=0`, namespace `«module».Sim`, file `Sp$D$module_jit.c` |
| `simcmd-dig` | `lean-errors=0` (before: a parse error at `namespace 1bad.Sim`), file `Sp$D$1bad_jit.c` |
| `simcmd lean` | process exit 0 (before: 1) |

## 3. Unit C — J2–J4: the C identifiers

### 3a. The encoding

`Sparkle/Backend/CIdent.lean` (new, pure, no import):

```
cIdent : Role → String → String
cIdent role m = "sparkle_" ++ code role ++ "_" ++ m
code:  structTag ↦ ms   reset ↦ mr   eval ↦ me   tick ↦ mt   evalTick ↦ mx
```

Role FIRST, as a code of fixed length (two letters) followed by `_`. Not a character substitution: the old
identifiers are not rewritten, they are produced by a different function of (role, module).

| claim | statement | established by |
|---|---|---|
| injective in (role, module), ALL strings | `cIdent r m = cIdent r' m' → r = r' ∧ m = m'` | PROVED (written): `Tools.ShippingCIdent.cIdent_injective`, from `cIdentL_injective` (`List.append_cancel_left`, `List.append_inj` with `code_length`, `code_injective` by cases) |
| struct tag ≠ any function; `eval` ≠ `eval_tick` of any module | `r ≠ r' → cIdent r m ≠ cIdent r' m'` | PROVED: `cIdent_role_ne` |
| starts with `sparkle_m` | `HasHead (cIdentL r m)` | PROVED: `cIdentL_hasHead` |
| never a string without that head | `¬ HasHead f.toList → cIdent r m ≠ f` | PROVED: `cIdent_ne_of_no_head` |
| no fixed name of the backend / keyword / libc name has the head | `fixedNames.all fun f => !f.startsWith "sparkle_m"` | `#guard` (`Tests/Compiler/CIdentTest.lean`); the step from `String.startsWith` to `HasHead` is by reading, not a theorem |
| pairwise distinct on a grid of 40 adversarial names × 5 roles | `gridIds.eraseDups.length == gridIds.length` | `#guard` (redundant with the theorem; evaluates the compiled function) |
| stable under `CSim.sanitizeName` | `sanitizeName (cIdent r m) = cIdent r m` for `m` over letters, digits, `_`, `$` | `#guard` on the grid ONLY; no theorem (the general lemma — `(cIdentL r m).all ok` from `m.all ok`, then the `if` of `sanitizeName` as in `Tools.ShippingModuleName.sanitizeName_encode` — is left for a worker) |

Why the three findings cannot recur: J2 needs `cIdent .evalTick X = cIdent .tick X_eval` — excluded by
injectivity; J3: the tag is `sparkle_ms_<m>`, never a keyword (head); J4: the trampolines `sparkle_jit_*`
keep their names and no `cIdent` equals one (head: character 9 is `m`, theirs is `j`).

Reserved identifiers: the head excludes a leading `_` (so `_X…` and a leading `__`), every C / C++ keyword,
`main`, and the library names the text uses (`memcpy`, `calloc`, `free`, `__builtin_memcmp`). NOT excluded:
`__` INSIDE the identifier when the module name has it (`Sp$D$always__ff`) — reserved in C++ only; the C
text is compiled as C (`-std=gnu11`), the CUDA text is C++ and UNVERIFIED. `$` in identifiers is a gcc /
clang extension the backend already relied on (measured with gcc 15.3 in the J rows).

### 3b. Every producer and consumer updated in commit C

| file:line | what |
|---|---|
| `Sparkle/Backend/CSim.lean:31` | `import Sparkle.Backend.CIdent` |
| `CSim.lean:1669–1672` (`emitStmt`, `.inst`) | instance field `struct <tag> <inst>;`, the child's eval / tick / reset calls |
| `CSim.lean:1947` | the module's `struct <tag>` |
| `CSim.lean:2079, 2096, 2112, 2179` | the four function definitions |
| `CSim.lean:2154–2176` (`instCalls`, `evalTickEvalBody`, `evalTickTickBody`) | the fused function: the child's eval identifier is replaced by its eval_tick identifier on the line of that instance (was: every `_eval(` → `_eval_tick(`), and the child's tick call is dropped by its identifier (was: `_tick(&self->inst)`). Same lines selected as before |
| `CSim.lean:2709–2717` and the trampolines below | `struct <tag>` (28 places), the four callees of the trampolines |
| `Sparkle/Backend/CudaSim.lean:75, 79` | `deviceStructName`, `deviceEvalTick` — UNVERIFIED |
| `Sparkle/Backend/CudaIntra.lean:261–412` | 16 `struct <tag>` in `offsetof` / signatures, `dispatchCases` now takes a `CIdent.Role` (`:325–328`, called at `:362`, `:368`) — UNVERIFIED |
| `Tests/TestCppSim.lean:256,286,291,298,348–351,362,365–366,369,376` | substring assertions on the C text (in the suite) |
| `Tests/TestCudaSim.lean:282–283,300–301,310–315,347,376–381,389–390` | substring assertions on the CUDA text (in the suite; text only) |
| `Tests/RV32/TestFlow.lean:64–67` | substring assertions on `verilator/generated_soc_cppsim.h` |
| `Tests/Drivers/SvCosimMain.lean:190,192,212,214`, `SmtBmcTestMain.lean:33,35,55,59`, `CudaIntraCosimMain.lean:93–116` | hand-written C `main`s over the generated struct and functions: now through `cIdent` |
| `Tests/Fixtures/symbolic_xor_csim.c.in` (12 `struct`, 4 calls) | C fixture of `scripts/verify_parameterized_csim.sh` |
| `scripts/shipping-coverage/tagged_names_sim.{lean,sh}` | rows `clibc`, `cpre`, `cmain`; comments |

NOT a consumer, by reading (no change): `Sparkle/Core/JIT.lean` and `c_src/sparkle_jit.c` — the externs
`sparkle_jit_*` there are symbols of the HOST binary; the generated shared object exports ONE symbol,
`jit_vtable` (`-fvisibility=hidden`, everything else `static`), and the loader `dlsym`s only that. The
trampoline names inside the generated text (`sparkle_jit_*`, `g_sparkle_jit_vtable`) are unchanged. The
vtable CONTENTS are unchanged (pointers to the same trampolines). `bench/bench_jit.cpp`,
`verilator/tb_jit_bench.cpp`: vtable only.

Left as they are, listed:
* `verilator/tb_cppsim.cpp:52–104`: uses the generated type as a C++ CLASS with methods (`soc.eval()`,
  `soc.tick()`) — already incompatible with the C backend's output before this change; not touched.
* `CSim.lean:2124–2129` (`rewriteSubEval`, `sparkle_evalTick_placeholder`): dead code (`let _ :=`), emits
  nothing; untouched.
* CUDA-only names made from the module name with a SUFFIX: `<top>_batch_kernel` (`CudaSim.lean:123,198,257`),
  `<top>_intra_{M,nCopies,nImms,off,kind,eval,eval_tick,cycles,block_kernel,grid_kernel}`
  (`CudaIntra.lean:345–400`): the J2 shape (a suffix after a module name). Not changed: they are made from
  the ONE top of a `.cu` file (no second module's name enters them) and are not shared with CSim; a top
  whose name ends like one of the suffixes of another identifier in the same file was not examined.
  UNVERIFIED and unimproved.
* `docs/CudaSim.md:24–26,39,56,214–219`, `docs/CudaIntraSim-design.md:72,128–129`: prose with the old
  scheme (`sparkle_<cls>_eval_tick`, `struct PE`); not rewritten.
* `<reg>_next` against a wire named `<reg>_next`, instance field `<inst>_inst`, member names equal to C
  keywords: rows of the J inventory outside J2–J4; untouched.

Compatibility: every generated C identifier of a module changes (`struct m` → `struct sparkle_ms_m`,
`sparkle_m_eval` → `sparkle_me_m`, …). Hand-written C that includes a `_cppsim.h` and names the struct or the
functions must be updated; in the tree that is the fixture and the three driver generators above. Generated
files on disk (`verilator/generated_soc_*`, `.lake/build/gen/**`) are stale until regenerated; the JIT cache
key is a hash of the C text, so no stale `.so` is reused.

### 3c. Regression

`Tests/Compiler/CIdentTest.lean` (elaboration time, no external tool, throws; suite-suitable — to add:
`import Tests.Compiler.CIdentTest`): the `#guard` grids; then the REAL `toCJIT` text of a real parent with
two children, modules RENAMED in the IR per row (`cfn`, `ckw`, `cjit`, `cmain`, `clibc`, `cpre`, `ctop`,
`ctag`), and in each text: every struct / function / trampoline defined exactly once, each child's eval,
eval_tick, tick and reset called exactly once (so the fused function calls eval_tick and does not tick the
child again); axiom audit of the six theorems. PREDICTED: pass. It does NOT compile C.

Driver rows (real declarations, gcc):

| row | before (measured) | PREDICTED now |
|---|---|---|
| `cfn` (`fk` + `fk_eval`) | `csim-cc exit=1`, `dup-funcs=[sparkle_TaggedNamesSimZZ_fk_eval_tick]` | `dup-funcs=[]`, `csim-cc exit=0`, `csim-run exit=0 c==source T` |
| `ckw` (`volatile`) | `csim-cc exit=1` (`struct volatile {`) | `csim-cc exit=0`, `c==source T` |
| `cjit` (`jit`) | `csim-cc exit=1`, duplicate `sparkle_jit_*` | `dup-funcs=[]`, `csim-cc exit=0`, `c==source T` |
| `clibc` (`memcpy`, new) | not run; by reading it passed (`struct memcpy`, `sparkle_memcpy_eval` are legal C) | `csim-cc exit=0`, `c==source T` |
| `cpre` (`sparkle_me_fk` + `fk`, new) | not run; by reading it passed | `dup-funcs=[]`, `csim-cc exit=0`, `c==source T` |
| `cmain` (module RENAMED to `main` in the IR, new; C rows only) | not run; by reading it passed (`struct main`, `sparkle_main_eval` are legal C) | `csim-cc exit=0`, `c==source T`; SystemVerilog rows `NOT RUN` |
| all J1 rows (`priv`, `kw`, `dig`, `alias`, `mem`, `uni`) | exit 0 with the J1 line | unchanged (`unqualified-inst-lines=0`; the script's pattern `\(&_tmp_inst` still matches an unqualified reference) |
| SystemVerilog rows of every row | — | unchanged: the SV emitter is not touched |
| `ckw verilator-cc` | exit ≠ 0 (measured: Verilator `--cc` on a module named `volatile`) | unchanged — a Verilator matter, not the C backend |

Honest note on the three new rows: by reading, `main` / `memcpy` / a prefixed name did NOT fail in the old
scheme (a struct TAG `main` and a function `sparkle_main_eval` are legal). They are regression rows for the
new scheme, not reproductions of a finding.

Suite tests whose assertions were rewritten (must still pass): `Tests.TestCppSim`, `Tests.TestCudaSim`,
`Tests.RV32.TestFlow` (the last reads a generated file: regenerate by building `IP.RV32.SoCVerilog`).

## 4. What to add (files I must not edit)

`lakefile.lean`:
```
lean_lib «Tools.ShippingCIdent» where
  roots := #[`Tools.ShippingCIdent]
```
`Tests/AllTests.lean`: `import Tests.Compiler.SimNamesTest`, `import Tests.Compiler.CIdentTest` (both run at
elaboration), and the three lines of §1 for the JIT rows. `Sparkle/Compiler/SimNames.lean` and
`Sparkle/Backend/CIdent.lean` are imported by `Elab.lean` / `CSim.lean` and need no entry.

## 5. How to run (integrator, serially, under cgrun)

```
# per unit: check out the commit, then
lake build Sparkle                                   # B: SimNames, Elab, SimChecked;  C: CIdent, CSim, Cuda*
lake build Tools.SVParser.SimMacro                   # B
lake build Tools.ShippingCIdent                      # C (after the lakefile entry)
lake build Tests.Compiler.SimNamesTest Tests.Compiler.SimIndexTest          # B
lake build Tests.Compiler.CIdentTest                 # C
lake build Tests.AllTests Tests.Compiler.CacheCoherenceProbe && lake exe test   # suite (+ TaggedJitE2E rows)
scripts/shipping-coverage/cgrun.sh -n tagged -m 3G -t 2400 -- scripts/shipping-coverage/tagged_names_sim.sh
scripts/verify_parameterized_csim.sh                 # C: the fixture
lake build sv-cosim smt-bmc-test cuda-intra-cosim    # C: the driver generators (lakefile.lean:1112–1139; they BUILD here, running them needs their tools)
```
Read in the driver output: `simdup`, `simrerun`, `simcmd-*` (B); `cfn`, `ckw`, `cjit`, `clibc`, `cpre`,
`cmain` `csim-ids` / `csim-cc` / `csim-run` (C). The C text of designs changes in EVERY row (identifiers);
compare functions (traces), not text.

## 6. What stays UNVERIFIED

* CUDA emitters (`CudaSim`, `CudaIntra`): no `nvcc`. Edited consistently with CSim (struct tag, eval /
  eval_tick identifiers); the suite checks SUBSTRINGS of the text only. C++ reserves `__` anywhere in an
  identifier; `$` in device code; the suffix names `<top>_batch_kernel` / `<top>_intra_*` — all unexamined
  by a compiler.
* `Verilator.of` for a tagged TOP (`Sparkle/Core/SimVerilator.lean:65,134`): the shim includes `V<top>.h`
  with a literal `$`, Verilator writes `__024` (measured: `literal-top-header F`). Not touched. Note that
  since unit B `#sim` on ANY declaration passes `svPath` with the `ofDecl` stem to it, so a tagged
  declaration's `.sv` FILE name now also has `$` (an argument, no shell) — not run.
* Vendor / FPGA flows, `synth_gowin`, the board; `bench/xiangshan` flows.
* The 27 `Tests/Drivers/*JIT*.lean` literal paths (their `#sim` sources are not in the tree).
* Designs parsed from external SV with `$` or keyword-like MEMBER names through the C backend.
* macOS (`.dylib`, a case-insensitive file system).

## 7. Could not be determined by reading

* Whether `private structure … deriving Repr, BEq, Inhabited` and `private instance : …` elaborate as
  generated here (row `simcmd-privself`), and whether the derived instances are private.
* Whether "already declared" from a generated `def` is THROWN through the nested `elabCommand` or only
  logged; the test accepts both (`cmdFails`).
* Whether a second `synthesizeHierarchical` of one declaration in one process prints the same C text (case
  iv, same environment).
* Port names of the E2E top (`_gen_x`, `out`) and the absence of a `rst` input on a combinational top.
* Whether a root declaration named `main` is accepted by Lean outside an executable (avoided: `cmain`
  renames in the IR).
* Kernel reduction details of the proofs: `by decide` on `¬ (['m','s'] = ['m','r'])` (the 20 off-diagonal goals),
  `⟨_, rfl⟩` for `HasHead` with the module name a variable, `String.toList_ofList` / `ofList_toList` as
  rewrite rules (the names are those `Tools/ShippingModuleName.lean` uses).

## 8. Risks, in order

1. **Private wrappers (B).** New generated text (`private def`, `private structure`, `private instance`)
   for a case that worked before (`#sim` on a private top, `simcmd-privself`). If refused: set
   `declIsPrivate` to `false` in the two commands (one line each) — wrappers public as before, paths still
   distinct.
2. **Scope handling (B).** `modifyScope` + `finally`. If the absolute namespace breaks name resolution in a
   user's context that worked before (identifiers of the wrappers resolved through the CURRENT namespace
   when the command was run outside the declaration's namespace), it shows as an elaboration error at the
   command. The eight in-tree users run the command inside the declaration's namespace: same constants.
3. **The fused-function rewriting (C).** The replacement key changed from the text `_eval(` to the child's
   whole eval identifier. If a line were selected by the marker but did not contain that identifier, the
   child would be evaluated but not ticked in `eval_tick` (a SILENT wrong result). By reading, the only
   line with `&self-><inst>)` is the call this file emits with exactly that identifier; `CIdentTest` asserts
   "eval_tick called once, tick called once" per child on nine texts, and unit A runs `eval_tick` on a
   parent with a child through the real loader (a combinational child: it would not see a missing tick). A
   sequential child under `eval_tick` is NOT covered by a new test — existing JIT suites with sequential
   children (`keccak256-sponge-jit-test`, `control-jit-test`) are the check.
4. **Consumers missed (C).** Any hand-written C outside the tree that names `struct <m>` or
   `sparkle_<m>_eval`. In the tree: the grep lists of §3b; `verilator/tb_cppsim.cpp` was already stale.
5. **Hand-computed strings in `#guard`s (B, C).** A wrong expectation fails the build of the TEST file only.
6. **Stale artifacts.** `.lake/build/gen/sim/<last>_jit.c` files of earlier builds remain; nothing reads
   them through the generated wrappers, but a driver with a literal path would silently load an OLD design
   if its `#sim` source now writes elsewhere (the 27 drivers of §2d).
7. **Proof file (C).** `Tools/ShippingCIdent.lean` is outside the compiler's import closure: if a proof
   fails, the compiler and the suite still build; only `CIdentTest`'s axiom audit depends on it.

## Integrator's build record (2026-10-14) — MEASURED; INTEGRATED on poc

Verified on the poc tree (35a3a91a + units B, C, D) as ONE STACK, run `stack2` (cgrun 3 GiB swap 0,
exit 0, peak 2.74 GB); the two fixes were not built one without the other. Worker's files unchanged,
first attempt. Integrator additions: the older comment near `isTokChar` now says `[A-Za-z0-9_$]`;
`lean_lib Tools.ShippingCIdent`; `SimNamesTest` and `CIdentTest` imported by `Tests/AllTests.lean`.

* `lake build Sparkle` (261 s), `Tools.ShippingCIdent`, `SimNamesTest`, `CIdentTest`, `Tests.AllTests`
  (full rebuild, 2136 s) — exit 0. `CIdentTest`: 8 texts (`cfn`, `cjit`, `ckw`, `clibc`, `cmain`, `cpre`,
  `ctag`, `ctop`), failed checks 0 each.
* Real JIT through the Lean FFI (`tagged-jit-e2e-test`): cycles=32 mismatches=0, both rows ✓.
* Existing JIT executables (sequential designs under the fused `eval_tick`): `crc32-jit-test` ALL PASS,
  `control-jit-test` ALL PASS, `keccak256-sponge-jit-test` ALL PASS.
* Driver (`tagged_names_sim.sh`, C main over the vtable): `cfn`, `ckw`, `cjit` — were `csim-cc exit=1`,
  now `exit=0`, `c==source T`; new rows `clibc`, `cpre`, `cmain` — `exit=0`, T; `priv`, `mem` still T.
* J5 rows: `simdup` (two files, two processes, same last component): each has its own file
  (`DupA_tnzDup_jit.c`, `DupB_tnzDup_jit.c`), A's content unchanged after B; `simrerun`:
  `same-path-same-content=T B-untouched=T lean-errors=0`; `simcmd-uni2` / `-kw` / `-dig`:
  `lean-errors=0`, stems `Sp$D$tnz_232_`, `Sp$D$module`, `Sp$D$1bad` (were a clash / refused).
* sims `writer_sim`, `module_name_sim`: exit 0.

Pre-existing, NOT caused by J5 and not touched: 26 files under `Tests/Drivers/` load
`.lake/build/gen/sim/<x>Top_jit.c` files that no declaration in the tree writes.
UNVERIFIED — not "all backends": the CUDA emitters (text changed consistently; no `nvcc`), the
`Verilator.of` shim for a tagged top, vendor / FPGA flows, case-insensitive file systems, the same
qualified name in two files never imported together, hash collisions for stems over 180 characters.
