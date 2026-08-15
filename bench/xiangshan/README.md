# XiangShan production-scale validation

Goal: prove Sparkle's SVParser → IR → backends pipeline at production scale,
using XiangShan (OpenXiangShan's out-of-order RISC-V) — the largest open
Chisel-generated RTL available.

## The two questions (in the user's words)

1. **Roundtrip fidelity**: XiangShan Verilog → Sparkle IR → Verilog again.
   Does the same RTL come back?  Any redundant logic introduced?
2. **Simulation competitiveness**: Sparkle CSim JIT vs Verilator on the
   same design — speed and correctness.

## Method

### Phase 1 — bring-up (MinimalConfig)
- `make verilog CONFIG=MinimalConfig` in the XiangShan checkout
  (needs JDK+mill: `nix shell nixpkgs#jdk17 nixpkgs#mill`).
- Feed each `build/rtl/*.sv` through `parseAndLowerFlat`; **catalog every
  parse/lower failure** with the construct that caused it.  This catalog IS
  the deliverable of phase 1 — it becomes the SVParser work list.

### Phase 2 — roundtrip metrics (objective, not eyeball)
For each module that parses:
- structural stats before/after: module/instance/register/wire/memory
  counts (Sparkle IR side vs original, via yosys `stat` on both);
- **redundancy metric**: `yosys -p "read_verilog; synth; stat"` cell counts
  original vs roundtripped — equal-ish cells = no redundancy introduced;
- per-module iverilog co-sim (the existing `iverilog-roundtrip-test`
  machinery) for behavioural equivalence on random vectors.

### Phase 3 — the big one (DefaultConfig / KunminghuV2)
Same pipeline at full scale; memory/time profiling of parse+lower+emit
(SPARKLE_PROFILE=1); fix scaling bottlenecks as found.

### Phase 4 — simulation shootout
`make emu` (Verilator) vs Sparkle CSim JIT on the same workloads
(ready-to-run/coremark), cyc/s and correctness vs NEMU difftest.

## Known-in-advance parser gaps to expect (Chisel/FIRRTL emission)
- SRAM blackboxes (`array_*_ext`) — need behavioural models or blackbox
  handling; DPI-C difftest imports — must be excluded at generation or
  stripped; `$fwrite`/assertion blocks; `always_ff`-style SV constructs.

## Phase 1 findings (2026-08-15, MinimalConfig, firtool-1.149.0)

Generated: 1,943 .sv files, 1.1 GB. Survey (`lake exe sv-roundtrip`):

- **74% parse+lower+emit OK** (1,438/1,940 excl. 3 giants), including
  files up to 3.5 MB.
- **502 parse failures**, construct histogram (the work list, priority
  order):
  1. **`N'(expr)` size casts** — `64'({33'h0, a} + b)` — the dominant
     class by far; firtool emits width casts everywhere.
  2. **Packed multi-dim arrays** — `wire [3:0][1:0] _GEN = {...}` +
     `'{...}` assignment patterns + dynamic element indexing
     (`_GEN[state]`); firtool's case-mux lowering idiom.
  3. Reduction operators in some positions (`{~(^(x))}` in dataCheck).
  4. A small instance-connection class (IntRFWBCollideChecker style).
- **Throughput**: linear ~4.6 MB/s/core on regular files; harness runs
  24-way parallel (round-robin over size-sorted files, incremental
  part-file catalogs).
- **Two construct-driven superlinear walls** (NOT byte-size-driven):
  PMP.sv (203 KB, deep nested compare/ternary chains) takes 22 s parse +
  22 s lower, vs 1.6 s + 1.9 s for a 3× larger regular file. Suspects:
  operator-precedence backtracking (`attempt`) in the parser, and a
  matching recursion in Lower. Emit is always ~0 ms.

Phase-1 work list, in order: (1) size casts, (2) packed dims + `'{}` +
dynamic element select, (3) parser/lower complexity on deep nesting,
(4) the long-tail classes. Then re-survey to 100%, then Phase 2 metrics.
