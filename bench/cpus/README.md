# Round-tripping open-source CPUs

`bench/xiangshan` validates the SystemVerilog front-end on firtool
output. This directory does the same on two hand-written / SpinalHDL
cores, whose Verilog style is different enough to expose different bugs:

| Corpus | Source (pinned) | Modules |
|--------|-----------------|---------|
| PicoRV32 | `YosysHQ/picorv32` @ `ef203c2` | 8 (core, PCPI mul/div, AXI and Wishbone wrappers) |
| VexRiscv | `litex-hub/pythondata-cpu-vexriscv` @ `642ecfe` | 19 pre-generated variants (Min … Linux, Secure), 54 modules |

Nothing is vendored; `fetch.sh` downloads the pinned commits.

## Running

```sh
bench/cpus/fetch.sh /tmp/cpus                 # sources → one module per file
systemd-run --user --scope -p MemoryMax=60G -p MemorySwapMax=0 \
  bench/cpus/run.sh /tmp/cpus                 # needs iverilog, gcc; ~10 min
```

`run.sh` does, per corpus:

1. `sv-roundtrip` — parse → IR → re-emit Verilog;
2. `sv-cosim` (leaf, then `--hier`) with `--zero-init` — the original
   under iverilog is golden; the re-emitted Verilog under iverilog and the
   C simulation of the IR must both match it for 300 cycles of
   deterministic random stimulus;
3. for PicoRV32, `picorv32_prog/run.sh` — an RV32I program
   (`picorv32_prog/fw.S`: loop, shifts, signed compare, byte/half/word
   stores and loads, a call, `ebreak`) runs on the original and on the
   re-emitted core; the memory-bus traces must be identical. Needs
   `riscv32-none-elf-gcc`.

It exits non-zero on any parse/lower failure, co-simulation mismatch, or
trace difference. It is not part of CI (it downloads sources and needs
iverilog); the minimal form of every bug it found is a unit test in
`Tests/SVParser/ParserTest.lean` (Tests 64–76), which CI runs.

## Result

| | modules | round-trip | co-sim agree (leaf + hier) |
|---|---|---|---|
| PicoRV32 | 8 | 8 | 6 + 2 |
| VexRiscv ×19 | 54 | 54 | 32 + 22 |

Every module is executed either as a leaf or with its instantiation
closure, including every complete core. The PicoRV32 program test passes:
154 bus transactions and the trap in the same cycle (594) on both sides.

Before this work none of the 19 VexRiscv files parsed, and the
round-tripped PicoRV32 mis-computed JAL and branch offsets.

## Regression checks for these changes

Run on the commit that added this directory:

- `lake build` and `lake test`: exit 0; `svparser-test`: 74 passed, 0 failed.
- XiangShan CI gate (`bench/xiangshan/ci_check.sh`): OK — 52/52 round-trip,
  co-simulation 35 leaf + 17 hierarchical agree, yosys equivalence 38
  proven / 12 unproven (induction limit, as in the baseline) / 0 errored,
  12 modules proven in the lean₄ round trip.
- Sparkle's own Verilog corpus (163 synthesis files): 6 files change, all
  by the `$unsigned($signed(a) >>> n)` emission. Under iverilog, the RV32
  ALU that main emits (`Sparkle.IP.RV32.aluSignal`) computes SRA of
  `0x80000000` by 4 as `0x08000000`; with this change it is `0xf8000000`.

## What it found

Parser
- `always @(*)` was destroyed by the `(* … *)` attribute stripper.
- `<<<` was not an operator.
- `$display(…)` inside an `if` made the enclosing statement unparsable;
  the always-block recovery then re-parsed the inner statements flat
  (VexRiscv DataCache lost its reset and its holds, silently). System
  tasks now parse; an unparsable statement is an error; an always block
  that still cannot be parsed is dropped only if nothing it assigns is
  used.

Lowering
- memories were recognised by name, not by declaration;
- part-select writes (`y[4:0] = 0`, `c[7] <= 1`) replaced the whole
  signal, and the first fix for that built a 2^n-node expression;
- a reset tested in a plain `@(posedge clk)` block became asynchronous,
  and registers not assigned in the reset branch were reset to 0;
- `>>>` on an unsigned operand was arithmetic;
- `$signed({…})` sign extension depended on where a left shift truncates;
- `.q(sig[31:0])` output connections were not read back by the C
  simulation.

Backends
- Verilog: `$signed(a) >>> n` inside a mux with an unsigned arm is a
  LOGICAL shift in Verilog; it is now emitted self-determined. This
  affects every design using an arithmetic right shift, not only
  ingested RTL.
- Optimizer: an unread register kept its `always_ff` but lost its
  declaration.

Harness (`sv-cosim`)
- X/Z in the golden trace is masked per output field, not per cycle;
- `--zero-init` zeroes registers and memories of the original (and its
  sub-instances) so both sides start from the IR's all-zero state;
- bus-style clocks (`wb_clk_i`) and common reset names are recognised.

## Known limits

- **Ibex / CVA6** are not covered: they need SystemVerilog packages,
  `import`, typedef'd structs and enums, which the parser does not read.
- The co-simulation stimulus is random, so a core usually traps on its
  first illegal instruction; only PicoRV32 has a program-level test.
- `$signed(x)` of a bare identifier is not sign-extended when assigned to
  a wider target (the width used is that of slices and concatenations).
- An output connection to PART of a wider signal (`.q(x[3:0])`) is not
  read back by the C simulation.
- The IR's left shift has no single width rule across backends (Verilog:
  context; CSim: grows by a constant amount; optimizer: left operand).
  The lowering avoids depending on it; the IR does not yet define it.
