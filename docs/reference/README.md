# Reference

Reference documentation — syntax, project setup, troubleshooting,
the verification framework, and the Sparkle ↔ Hesper equivalence
work.

## Sparkle DSL

- [`SignalDSL_Syntax.md`](SignalDSL_Syntax.md) — Signal DSL syntax
  reference: operators, combinators, `Signal.circuit do`, the full
  list of macros and commands.
- [`How_To_Use.md`](How_To_Use.md) — how to start a stand-alone
  project that imports Sparkle.  Covers `lakefile.toml` and
  `lakefile.lean` flavours, `lean-toolchain`, library and
  executable targets.
- [`Troubleshooting_Synthesis.md`](Troubleshooting_Synthesis.md) —
  the canonical list of synthesis-safe and synthesis-unsafe
  constructs.  Read this before writing serious Sparkle code.

## Verification

- [`Verification_Framework.md`](Verification_Framework.md) — the
  proof framework.  Safety (mutex, buffer overflow), liveness
  (starvation-freedom, deadlock), efficiency, and the
  `#verify_eq` family.
- [`Hesper_Equivalence.md`](Hesper_Equivalence.md) — Sparkle ↔
  Hesper cross-stack equivalence proofs (BitNet matmul + attention).

## Project conventions

- [`CommitStyle.md`](CommitStyle.md) — Git commit message style
  for Sparkle PRs.
