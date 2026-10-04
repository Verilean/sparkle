# Architecture

How Sparkle compiles Lean to SystemVerilog and to a C++ JIT, and
the system-level design notes for the larger SoCs.

- [`STATUS.md`](STATUS.md) — append-only development log.
  Current phase, completed milestones, JIT vs Verilator benchmarks.
- [`RV32_Architecture_Status.md`](RV32_Architecture_Status.md) —
  RV32 SoC pipeline structure (3-stage, M-extension, Sv32 MMU,
  timer/CLINT integration).
- [`CDC.md`](CDC.md) — Clock-domain-crossing design.  Lock-free
  SPSC queue, multi-threaded JIT, formal rollback proofs.
- [`JIT_FFI_Plan.md`](JIT_FFI_Plan.md) — How the C++ JIT integrates
  with Lean.  `sparkle_eval_at`, memoised loop, codegen.
