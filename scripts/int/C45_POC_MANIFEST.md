# C4/C5 poc integration candidate: frozen manifest (before builds)

Issue `sparkle-int-c45-poc` (milestone `sparkle-gen`). Local candidate only.
- Merging into poc needs explicit user approval after review.
- No CI claim.

## Base, source, candidate
- **Base:** `poc/roundtrip-proof` 0054b6b2e0ffa4b65b064ee7b8be4e0eb59e38b7.
- **Source:** accepted C5 integration `kjob/c5-int` a942e6ac.
  - It contains the accepted C4 integration 692d78e3 (C4 is an ancestor).
  - Review records:
    - C4 `memSharedLeaf_ships`: approved at 692d78e3, final build c4-final-692d78e3, 981/981.
    - C5 `qSharedLeaf_ships`: approved at a942e6ac, final build c5-final-a942e6ac, 981/981.
- **Merge base:** merge-base(0054b6b2, a942e6ac) = 0054b6b2, so poc is an ancestor of the source.
  - The source is 605 commits ahead, including 24 no-ff merges of accepted units.
  - The full history is carried as-is; it was integrated and accepted by those reviews. No commit is
    cherry-picked or rewritten.
- **Candidate:** branch `par/int-c45-poc`, worktree ~/git/.kjob/int-c45-poc.
  - Merge commit cd58080e2a50a7ac384e8dea9d33a8acfdc0a7ed: `git merge --no-ff a942e6ac` on 0054b6b2.
  - Its tree equals a942e6ac's tree, checked with `git rev-parse` on both trees.
  - This manifest is then committed as a docs-only freeze commit. That commit is the build head.

## Changed paths (0054b6b2 → candidate)
- **Scale:** 596 files, +124304 / −41.
- **Nothing under Sparkle/, IP/, Examples/, Main.lean, lean-toolchain or lake-manifest.json changes:** no
  compiler or production change.
- **Modified pre-existing files (11):**
  - `Tests/AllTests.lean`: +37, new imports.
  - `Tests/Compiler/ChildVertAuditTest.lean`: audit roots.
  - `Tools/ShippingChildFallbackA.lean`, `Tools/ShippingMachineCommand.lean`, `Tools/ShippingMachineDepthRun.lean`,
    `Tools/ShippingMachineDepthRunR.lean`, `Tools/ShippingMachineEntry.lean`, `Tools/ShippingSatAssemblyS.lean`.
  - `lakefile.lean`: +1108, additive `lean_lib` entries only.
  - `docs/parallel/O-origin-integration.md` and `docs/parallel/open-items-by-kind.md`.
- **Added:** everything else is a new file under Tools/, Tests/, scripts/ or docs/.

## Lean module inventory and targets
- **Graph scan:** reverse-import closure over `^import` lines of every `.lean` file in the candidate tree.
  The script is in the review note; it is not committed.
- **Changed modules:** 418, listed in `scripts/int/C45_CHANGED_MODULES.txt`, SHA-256
  `5ded01269d3d00a94cde17c3bf2fcef1997a18304283cc527d317ae70ad1084c`. That count includes `lakefile` and
  `scripts.*` `.lean` files.
- **Closure:**
  - The transitive importer closure of the changed modules has 1141 modules.
  - 737 of them are in the `Tests.AllTests` import closure.
  - The other 404 are outside it. Of those, 10 are `lakefile` and `scripts.*` files, which are not lake modules
    and are excluded.
- **Extra targets:** the remaining 394 are frozen in `scripts/int/C45_EXTRA_TARGETS.txt`, SHA-256
  `ddb8eeb4bcf6dad4b3339614d740e4f85b55ada7c75b5c526bcbaa4b6ff805b6`.
  - Every one is a buildable lake module. The 282 `Tools.*`/`Tests.*` modules have their own `lean_lib`
    entry.
  - The other 112 are all `Tests.*`, buildable through `lean_lib «Tests»` (root `Tests`;
    `isBuildableModule` = root prefix + glob on the root, Lake v4.32.1 Config/LeanLibConfig.lean:127-130).
    105 of those 112 already existed at 0054b6b2.
- **What the targets cover:**
  - `Tests.AllTests`, which covers its 737-module part of the closure, including `ChildVertAuditTest`.
  - The 394 extra targets, which include `Tests.Compiler.C4FinalTest` and `Tests.Compiler.QFinalTest`.

## Builds (all issue-linked, exact head, head = base, dirty = false)
Command shape:
`kjob -N sparkle-dev run -d --issue sparkle-int-c45-poc --name <job> -n <node> -m 12Gi -c 4 -- kjob lake build sparkle_barrier sparkle_jit <targets>`.

| job | targets |
|---|---|
| `c45-all-<sha8>` | `Tests.AllTests` |
| `c45-x00-<sha8>` … `c45-x09-<sha8>` | extra targets in order, 40 per chunk (lines 1-40, 41-80, …, 361-394) |

- **Node placement:** at most one heavy build per node (mkvs-dell, mkvs-macpro, hayabusa).
- **Polling:** every 10 minutes. Running jobs are never cancelled or restarted.
- **Failed jobs:** they are recorded as diagnostics.
  - An OOM chunk is split in halves with new job names.
  - A wrong-cwd or dirty run is excluded and rerun under a new name.
- **Failure classification:** a nonzero target is a failure until the same target is built at base
  0054b6b2, if it exists there, and fails the same way.
  - The known baseline non-passes `Tests.Compiler.KeccakSpongeStepProbe` and `Tests.Compiler.SingleOutStaleProbe`
    are not counted as passes.
  - If either appears in the frozen list, it is classified by the base comparison.

## Scope / not claimed
- This candidate integrates accepted C4/C5 general theorems.
- G3 remains an exact-gap settlement (bridges OPEN).
- No new theorem, no CI, no production change.
- No merge into poc without explicit user approval after review.

## Build evidence (source head 7c70632c; recorded in a later docs-only commit)
All builds below ran at source head 7c70632caa90ec74f065eb841c661b06dccb3ba7. For each job, `kjob result` reports:
- head = base_head = source_head = end_head = 7c70632c;
- dirty false, ancestry_verified true, candidate_commits [];
- issue sparkle-int-c45-poc, runner da50a69b.

This evidence section is a later docs-only commit. Its SHA is not the build head.

| job | node | exit | lake jobs | failing target |
|---|---|---|---|---|
| c45-all-7c70632c | mkvs-dell | 0 | 1687 | - |
| c45-x00-7c70632c | mkvs-macpro | 0 | 1880 | - |
| c45-x01-7c70632c | hayabusa | 1 | (1009) | `Tests.Compiler.KeccakSpongeStepProbe` only |
| c45-x02-7c70632c | mkvs-dell | 0 | 1103 | - |
| c45-x03-7c70632c | mkvs-macpro | 1 | (1768) | `Tests.Compiler.SingleOutStaleProbe` only |
| c45-x04-7c70632c | hayabusa | 0 | 996 | - |
| c45-x05-7c70632c | mkvs-dell | 0 | 1002 | - |
| c45-x06-7c70632c | mkvs-macpro | 0 | 1025 | - |
| c45-x07-7c70632c | hayabusa | 0 | 611 | - |
| c45-x08-7c70632c | mkvs-dell | 0 | 712 | - |
| c45-x09-7c70632c | mkvs-macpro | 0 | 963 | - |

`Tests.AllTests` and 392 of the 394 extra targets pass. Each of the two failing jobs has exactly one `✖` line, for the
target named above.

### Failure classification (base comparison at 0054b6b2)
Both base builds ran at 0054b6b2 in the detached worktree ~/git/.kjob/c45-base, with head = base = end = 0054b6b2, dirty
false and runner da50a69b. Both probe files are byte-unchanged between 0054b6b2 and 7c70632c.
- **`Tests.Compiler.KeccakSpongeStepProbe`:** `c45-base-keccak-0054b6b2` exits 1 with the same error lines as x01:
  - a Type mismatch at 632:2;
  - unexpected token 'needs' at 632:85;
  - elaboration functions not implemented at 719/725.
  
  It is a baseline non-pass.
- **`Tests.Compiler.SingleOutStaleProbe`:** `c45-base-sostale-0054b6b2` exits 1 with the same error as x03:
  `107:0: SINGLEOUT: the two modules are EQUAL — the prediction is wrong (DetN is not refuted by this mechanism)`.
  It is a baseline non-pass.

Neither failure is introduced by the integration. Both are counted as non-passes, not passes.

### Whitespace note (not a target failure)
`git diff --check 0054b6b2 7c70632c` reports trailing-whitespace lines. All of them are inherited from the accepted
a942e6ac: `git diff --check a942e6ac 7c70632c` is empty. This is a hygiene note only and is unrelated to the two
probe failures above.

### Status
Ready for review. No merge into poc and no push without explicit user approval. No CI claim.
