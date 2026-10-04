# Hesper PR — pure-Lean DSL evaluators

This directory vendors copies of two pure-Lean evaluators that we
want to upstream into [Verilean/hesper](https://github.com/Verilean/hesper):

  - `CircuitInterp.lean` — evaluator for `Hesper.Circuit.ScalarExp`
  - `WGSLInterp.lean` — evaluator for `Hesper.WGSL.Exp` (full Phase-4
    coverage: stateful atomics, real textures, 4×4 determinants,
    typed bitcast)

A PR-ready feature branch lives at `/tmp/hesper` (branch
`feat/lean-evaluators`) with the upstream-shape versions of these
files. To open the PR:

```bash
cd /tmp/hesper
git push -u origin feat/lean-evaluators
gh pr create --title "Add pure-Lean reference evaluators for Circuit IR and WGSL DSL" \
  --body-file /tmp/hesper-pr-body.md
```

## What's in the PR

3 commits, +727 / −258 lines:

| Commit | Files | Purpose |
|---|---|---|
| 1 | `Circuit/IR.lean`, `Circuit/IRCore.lean` (new) | Refactor: split pure data types out of IR.lean |
| 2 | `Circuit/Eval.lean` (new) | Reference evaluator for `ScalarExp` + Prim helpers |
| 3 | `WGSL/Eval.lean` (new), `Proofs/EvalSanity.lean` (new) | Phase-1 WGSL evaluator + sanity tests |

## Why a refactor in commit 1?

Upstream `Hesper/Circuit/IR.lean` `imports Hesper.Backend` and
`Hesper.Layers.Linear` even though the pure IR (DType, Scope,
ScalarExp, ReduceOp) doesn't actually use any GPU-side symbols.
That transitive dep means pure-Lean tooling — like the new
evaluators — can't build without Dawn / WebGPU / X11.

Commit 1 splits the pure data into a new `IRCore.lean` and leaves
the GPU-flavoured `Prim`/`CircuitM` in `IR.lean`. No public symbol
moves namespace; `import Hesper.Circuit.IR` still works for every
existing user.

## Phase difference

This PR ships **Phase 1** of the WGSL evaluator (the BitLinear /
attention slice — about 50 of 225 constructors). The Sparkle copy
in this directory has the full **Phase 4** coverage:

  - All 225 upstream constructors with concrete eval arms.
  - State-passing `Exp.evalSt` for atomic ops.
  - Texture sampling against env-resident image data.
  - Full 4×4 cofactor-expansion determinant.
  - IEEE-754 typed bitcast via `Float32`.

Why not upstream Phase 4 directly? Two reasons:

  1. The upstream `Exp` AST doesn't have a `mat4x4_f32` value
     constructor (only the type), so the 4×4 determinant test
     can't be expressed without a small constructor extension.
  2. The state-passing evaluator's API is best co-designed with
     existing Hesper users that consume atomics; doing it as a
     follow-up keeps this PR reviewable.

Both are listed as Phase-2 follow-ups in the PR body.
