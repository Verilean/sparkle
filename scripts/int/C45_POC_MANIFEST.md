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
