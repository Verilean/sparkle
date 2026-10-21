# Perf: Tools/ShippingBundleIotaRange.lean (unit PF, measurement only)

Base 37a0ec34. Module not edited. Scratch copies: Tests/Compiler/PFProbe{0,1,2}.lean (not registered, removed before commit).
Method: `./.cluster/qbuild.sh env lean <file>` (lake env lean on the file, same imports and toolchain as the real build), node mkvs-dell.

## Measured (all exit 0)
| run | what | wall |
|---|---|---|
| pf1 | whole module body, `profiler true`, threshold 500 ms | 70.3 s wall, 110.6 s user (158% CPU) |
| pf2 (part 1) | the two imports only (PFProbe0) | 0.57 s |
| pf2 (part 2) | whole module body, `trace.profiler` threshold 1 s | 66.0 s wall, 121.6 s user |

**The module builds in about 66-70 s wall (about 110-120 s CPU) on an otherwise idle slot, not 480 s.**
I could not reproduce 480 s. The measured numbers are what this node gives for the SAME proofs and imports;
the gap (about 7x) is not explained by anything in the file. My best (UNVERIFIED) explanation is machine load /
contention during int-r22a (several lake jobs, cold NFS .olean reads), plus the integrator building through
`lake build` with other modules in parallel. Please re-time the real `qbuild.sh build Tools.ShippingBundleIotaRange` once on a quiet slot to confirm;
I did not run it (it would also write .olean files into this worktree's .lake).

## Attribution (cumulative profiler, pf1)
simp 51.5 s, tactic execution 18.4 s, dsimp 9.2 s, typeclass inference 9.0 s, kernel type checking 2.1 s,
linting 1.1 s, elaboration 0.5 s, pre-definitions 0.95 s. So it is elaboration-time tactic work, not kernel and not code generation
(all declarations are `theorem`s; no codegen of defs; `dite_goal` is a theorem too).

Per declaration (trace.profiler, `Elab.async`; proofs elaborate in parallel, so these overlap):
- `bundleIota_key2` 63.1 s  (long pole: it determines the 66 s wall)
- `bundleIota_key1` 23.0 s
- `bundleIota_key3` 19.0 s
- `bundleIotaRange` 12.4 s
- the primed corollaries and `dite_goal`: negligible (< 1 s each; below threshold).

Inside each proof the cost is in the `case const` branch after the `rcases nm` name-tree split (the product of the Name-spine
cases × the pattern cases). In key2: `all_goals` blocks 42.8 s of 61.3 s. Top single steps:
`all_goals (repeat' split)` 9.1 s and 6.8 s (the two `repeat' split` passes; individual `split` calls that fail "💥" cost up to 4.6 s per goal
at the simp step limit), and the big `all_goals first | exact he | (exfalso; simp at *; done) | (simp [he]; done) | ... simp_all [...]` chains 7.4 s / 5.5 s.
Individual `simp` calls reach 2-3 s (four of them 2.0-3.0 s). Linter notes: the `simp [he]` and `simp_all [Array.getLit, LetOk]` arguments are unused
(harmless, but a sign the `first` alternatives are tried blindly).

## Why dependents were rebuilt in int-r22a
Import graph (grep over Tools/ and Tests/Compiler):
- `Tools.ShippingBundleIotaRange` imports `ShippingLetsReaderInvMain`, `ShippingSparseCasesTac`.
- It is imported ONLY by `Tools.ShippingLetsExternSpec` and `Tests/Compiler/ChildVertAuditTest.lean`.
- `ShippingLetsExternSpec` imports it and `ShippingLetsSigTy`, and is imported only by the audit test.
So the chain is ReaderInvMain/SparseCasesTac -> BundleIotaRange -> ExternSpec -> ChildVertAuditTest. Lake rebuilds a module when its source or any imported .olean hash changes:
any edit to ReaderInvMain/SparseCasesTac/BundleIotaRange (or ExternSpec in r22: commit e9e2686f touched ExternSpec) rebuilds everything downstream,
including the audit test, which also imports ~30 other modules and runs the `#print axioms` list. The 18 min audit therefore is "this module (~1-8 min depending on load)
+ ExternSpec + the audit file's own elaboration", not a re-run of anything that merely imports the audit. The audit imports it directly; KEEPING the audit coverage, there is still room to examine dependency separation (moving the module off the audit's critical path) and caching of intermediate build results — not evaluated here.
Not verified here: the exact build logs of int-r22a, so the split of the 18 min between these modules is an inference.

## Speed-ups (same statements, same audit coverage). NONE MEASURED beyond baseline: I was told not to edit the file and did not build variants.
1. Split `bundleIota_key2` (the long pole): its 4-way product (nm × H × k × pattern) is elaborated in one proof, 63 s. Lemmas per scrutinee
   case (e.g. the `Prod.fst`/`Prod.snd` head test separated from the `bundle2` argument test) would cut the case product and
   let the four proofs run in parallel anyway; wall time is bounded by key2, so key2 is the one that matters. Expected: wall from ~66 s toward ~25 s (estimate, not measured).
2. Replace the second `repeat' split` and the trailing `first` chains by `simp only [...]`/`rfl`-style closers for the cases that actually occur;
   the `first` list shows that most branches close with `exact he`, so putting the cheap `exact he` before any `split` (`all_goals (try exact fun _ => he)` already exists; a third early attempt after `dsimp only`) avoids `split` failing at the simp step limit (4.6 s per failing goal).
3. Drop the unused simp arguments (`he`, `LetOk` per linter): trivial, little effect.
4. `set_option maxHeartbeats`/`maxRecDepth` are already raised, so nothing to gain from there; do NOT use `decide := true` or `native_decide` (forbidden, and no decide in the file).
5. Process: the audit test cost is dominated by the dependency chain; keep ReaderInvMain/SparseCasesTac stable, and edit ExternSpec/audit only (they do not force this module to rebuild; only upstream changes do).

OPEN: reproduce the 480 s on the integration node under load; measure variants 1-2 (needs a copy of the file with key2 split; statements unchanged).

Note (integrator, from the review): the 66–70 s measured here were on dell with a scratch `lean` invocation; the 480 s in int-r22a were a `lake build` on macpro — different conditions. The cause of the difference (load, environment) is NOT verified. The estimated ~25 s saving is an estimate, not a result.
