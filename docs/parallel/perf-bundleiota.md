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

## PF2: measured variant of `bundleIota_key2` (unit PF2, base 9e1db4c1)

Environment (all runs identical): node mkvs-dell, 32 cores / 62 GB, `./.cluster/qbuild.sh env lean <file>` (= `lake env lean`, single
elaboration thread in practice: user ≈ wall for key2 alone), same imports, sequential, slot held by this worker. Scratch files
(`Tests/Compiler/PF2*.lean`, unregistered, removed before commit). The original file was NOT edited.

**Cause found (measured, not estimated).** Counting goals with `trace` markers: after the `rcases nm/H/hn/k` and the `repeat' split`
passes, 456 goals remain, each of the form `(∀ a ∈ ⟨L⟩, LetOk n a = true) → LetOk n (h₁ ▸ h₂ ▸ h₃ ▸ h₄ ▸ Eq.rec … e) = true`
with `h : s3 = "Sparkle"`, … still hypotheses on *variable* strings. The casts do not reduce, so `exact fun _ => he` and `dsimp only`
cannot close the (default-arm) goals; all 456 are then multiplied by the 9-way `rcases L` → 4104 goals reaching the big `first … simp at * / simp_all`
chain (32 s of the 45 s traced). Adding `subst_vars` makes the casts reduce, the default-arm goals close at once, and only 168 goals survive to the chain.

**Change (one line, key2 only, statement and the rest of the proof untouched):** insert `all_goals (try subst_vars)` immediately before the
second `all_goals (try dsimp only)` of `bundleIota_key2`:

```diff
     all_goals (try rcases k with _ | _ | _ | k)
+    all_goals (try subst_vars)
     all_goals (try dsimp only)
     all_goals (repeat' split)
```
(Equivalent to `git diff` of Tools/ShippingBundleIotaRange.lean at line 163. A further variant that also shortens the `rcases nm`/`rcases hn`
name trees (5 / 3 levels instead of 6) measured 15.2 s for key2 alone vs 18.6 s for the one-line change; not proposed, larger diff.)

**Measurements** (wall, seconds; exit 0, 0 errors in every run):

| what | runs | 
|---|---|
| key2 alone, ORIGINAL | 51.9, 51.0 |
| key2 alone, one-line change | 18.6 |
| key2 alone, one-line + shorter name trees | 15.5, 15.2 |
| WHOLE module copy, ORIGINAL (`PF2FullOrig`) | 52.3, 52.3, 52.8 |
| WHOLE module copy, one-line change (`PF2FullNew`) | 20.6, 20.9, 20.7 |

Whole-module wall on this node/command: ≈52.4 s → ≈20.7 s (about 2.5x). (The 66–70 s in the earlier PF section used another run of the same
scratch-`lean` method; same-session baseline here is 52 s. The 480 s `lake build` on macpro is still not reproduced or explained.)
Not measured: `key1`/`key3` (same shape, likely the same fix applies; after the change they, at ≈19–23 s, become the long pole); a `lake build`.

**Checks.**
- Statement: the diff is a single inserted tactic line inside the proof of `bundleIota_key2`; the signature/type text is byte-identical, and the whole module
  (including `bundleIotaRange`, which applies `bundleIota_key2` to a goal of the original type) elaborates with exit 0.
- Axioms (`#print axioms`, from the whole-module scratch run, both ORIGINAL and CHANGED): `bundleIota_key2` and `bundleIotaRange` depend on `[propext, Quot.sound]`.
- No `sorry`, no new axiom, no `native_decide`; same theorem names, so the ChildVertAuditTest list is unchanged.
- PROPOSAL only: not applied to Tools/ShippingBundleIotaRange.lean; the integrator must review, then run a normal `qbuild.sh build Tools.ShippingBundleIotaRange` and the audit.

Integration (par/int-r26): the one-line change is applied to Tools/ShippingBundleIotaRange.lean (key2 only; key1/key3 untouched — not
measured). Its confirmation is the normal `lake build` + audit of the integration run. Scope: this is a measured speed-up of key2 in
one environment (dell, scratch `lean`, 52 s → 21 s whole module); it does NOT explain the 480 s seen in int-r22a, and no overall
factor is claimed.
