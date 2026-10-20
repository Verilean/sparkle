# Finding H fix (injective module names): integration record, 2026-10-13

Verified tree `e069b9b337dd86c9b1c23e49c9fba86822cd90df` = poc c385ae5c (C1) + worker A's C2–C5
(`fix/module-name-injective` 2fff13a5, 8c718b78, 3465696a, de17c631, 6db12626, cherry-picked without
conflict) + the integrator's hand fixes below + `ModuleNameInjectiveTest` in `Tests/AllTests.lean`.
Built in the isolated worktree `~/sparkle-work/wt-cachefix` (branch `fix/module-name-build`); every run
through `cgrun.sh`, 3 GiB, swap 0, one job. GitHub CI: 0 runs for this head — no CI result exists.
The specification, the encoding table, the sites and the open list are in
`docs/parallel/H-fix-injective-names.md` (worker A, written before any build) and `H-fix-c1.md`.

## Runs

| run | what | exit | peak |
|---|---|---|---|
| `20261013-164836-h-c2-sparkle` | `lake build Sparkle` (the five compiler sites) | 0, 209 jobs | 1.74 GB |
| `20261013-165237-h-c2-sample` | 28 corpus files on poc c385ae5c and on the worktree | 0 | 0.56 GB |
| `20261013-165716-h-c3-all` | `lake build Tests.AllTests ModuleNameInjectiveTest CacheCoherenceProbe` | 1 (4 files) | 2.46 GB |
| `20261013-172554-h-c3-all2` | the same after fixes | 1 (2 files) | 1.18 GB |
| `20261013-173253-h-c3-all3` | the same + sims | 1 (1 file; sims not started) | 0.75 GB |
| `20261013-173333-h-c3-all4` | the same + 5 further tests, then the five sims | 0, 1290 jobs; every sim exit 0 | 0.52 GB |
| `h-int` | `lake build Tests.AllTests` with the new test imported | 0, 1288 jobs | 0.44 GB |

## What changed in emitted text (SAMPLE, not the corpus)

No full-corpus measurement was run (standing instruction). 28 corpus files that import only the compiler
library (`~/sparkle-work/hfix-sample/files.txt`: sub-modules, memories, loops, circuit do) were run with the
old and the new compiler. Exit statuses equal (25 ran, 3 fail identically on both trees — two on a missing
olean of an import; the third, `Tests/VerifyVerilog.lean`, not looked at, no diff). `compare_outputs.py`:
9 outputs identical, 20 different; every differing line is one of

* the `// Module:` comment (`Sparkle.IP.X.f` → `Sparkle_IP_X_f`; `Module.name` is now the identifier);
* diagnostics quoting the module name (DRC warnings, "N sub-module instance(s)");
* the path in the two missing-olean messages;
* TWO REAL IDENTIFIER CHANGES, of 91 emitted `module` headers: the `private` declarations of
  `IP/Crypto/AESHW.lean`, `_private_IP_Crypto_AESHW_0_Sparkle_IP_Crypto_AESHW_synth_aesSbox` →
  `Sp$D$__private$IP$Crypto$AESHW$_0$Sparkle$IP$Crypto$AESHW$synth__aesSbox` (and `…aesRcon`).

So: a `private` declaration (its `Name` has a numeric component and a `_private` head) is not "plain" and
now gets a tagged `Sp$D$…` identifier. No script or RTL in the repository refers to those two names.
`$` in identifiers: accepted by iverilog in `module_name_sim.sh`; NOT checked under yosys, the C JIT,
Verilator or any vendor tool.

## Behaviour change: names that were refused are now compiled

`Tests/Compiler/ShippingModuleNamesTest.lean` asserted "Invalid or colliding Verilog module names" for
declarations named `module`, `1bad` and for a parent of `a.b` and `a_b`. The success domain is WIDER now:
the test asserts that `module` / `1bad` compile under `ofDecl`, a legal non-keyword name, and that the
design of `ModuleAlias.top` has the two children under two names, no duplicates, also after
`sanitizeName`. `validateDesignNames` itself is unchanged and still refuses hand-made colliding designs.

## Finding H's four tops

`Tests.Compiler.ModuleNameInjectiveTest` (asserting, in AllTests): `nTop`, `nDirect`, `mTop` — the two
declarations that printed alike are two modules (`Sp$D$_35_ccp_46_k` adds 1, `Sp$D$_35_ccp$k` adds 2),
each parent instantiates its own, 0 cache clashes; `mmTop` — the declaration `SparkleMem.combo.4.8`
(`Sp$D$SparkleMem__combo__4__8`) and the memory module `SparkleMem_combo_4_8` are different modules.
`scripts/shipping-coverage/module_name_sim.sh` (run `h-c3-all4`): the real writer output of the four tops
compiled by iverilog, `command==source T`, 0 x-cycles, 94 cycles each, one stimulus. BEFORE the fix
Finding H was read from the IR and the text, never simulated; that distinction stays.

Existing sims on the same tree: `writer_sim` 7 designs new==source T old==source T; `nested_let_sim` 3 T;
`optprint_sim` 12 of 12 T; `subinst_key_sim` 5 T. `DepthSwitchPinTest`: 51 of 51 fingerprints equal to
the table (a fingerprint, not defEq).

## Integrator's hand fixes (places the substitution missed)

* `Tools/ShippingKidsChildIface.lean` `namesOf`: `(·.1.toString)` → `ofDecl`.
* `Tests/Compiler/LegacySemInstanceTest.lean` (9 statements), `LegacySemMemoOuterTest.lean` (2):
  `(``f : Name).toString` / `xName.toString` as the entry's module name → `ofDecl`. The `sorryAx` reports
  of the first runs were consequences of those failed proofs; gone in `h-c3-all4` (audits pass).
* `Tests/Compiler/ShippingMachineSeqTest.lean`: top looked up by `name.endsWith ".parent"` → `== ofDecl`.
* `Tests/Compiler/ShippingModuleNamesTest.lean`: above.
* `Tests/Compiler/NoPortsMixDeepTest.lean`: one quoted hypothesis in a comment.

## NOT claimed

* Cache coherence. Injective names remove "two declarations, one name" as a counterexample; whether one
  `Name` can give different results under different contexts / routes / cache states is a separate
  obligation (initial → preserved → consumed), unproved. `mixDeep` is still open. No `Fits` / `ChildBndC`
  hypothesis was added or made ALLOWED.
* No endpoint lost a premise by this change. The endpoints still carry their name premises, now about
  `ofDecl`; discharging them from `ofDecl_injective` / `ofDecl_ne_ofMem` is a follow-up.
* Legality of every image as an SV identifier and "plain image = the old identifier": tested, not proved.
* External / primitive module names (user strings) are in no tagged namespace.
* `#sim` file names by last component; not touched.
* The whole corpus: only the 28-file sample and AllTests.
