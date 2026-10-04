# Sparkle Documentation

Sparkle is an HDL DSL embedded in Lean 4: write hardware in Lean,
synthesise to SystemVerilog or simulate via a JIT-compiled C++
backend, and prove correctness with Lean's tactic language.  This
directory holds the documentation, organised by audience.

## Tutorial — start here

The 11-chapter beginner course covers Lean syntax for HDL authors,
combinational and sequential logic, modules and composition, Verilog
generation, LTL invariant proofs, equivalence checking, Yosys
netlist generation, FPGA bring-up (iCE40 + ECP5), and a tour of the
Sparkle compilation pipeline.

| Chapter | What it covers |
|---|---|
| [`Ch00_Setup.md`](tutorial/md/Ch00_Setup.md) | Setup — Docker image or local install |
| [`Ch01_LeanForHdl.md`](tutorial/md/Ch01_LeanForHdl.md) | Just enough Lean to read the rest |
| [`Ch01b_YourFirstProject.md`](tutorial/md/Ch01b_YourFirstProject.md) | Stand-alone project layout |
| [`Ch02_Combinational.md`](tutorial/md/Ch02_Combinational.md) | AND/OR/MUX/half-adder, Verilog comparison |
| [`Ch03_Sequential.md`](tutorial/md/Ch03_Sequential.md) | Flip-flops, counters, FSMs |
| [`Ch04_Modules.md`](tutorial/md/Ch04_Modules.md) | `declare_signal_state`, hierarchical design |
| [`Ch05_Verilog.md`](tutorial/md/Ch05_Verilog.md) | `#synthesizeVerilog` walk-through |
| [`Ch06_LTL.md`](tutorial/md/Ch06_LTL.md) | Invariants and K-cycle preservation |
| [`Ch07_Equivalence.md`](tutorial/md/Ch07_Equivalence.md) | Equivalence checking via `decide` |
| [`Ch08_Yosys.md`](tutorial/md/Ch08_Yosys.md) | Netlist generation, gate counts |
| [`Ch09_FPGA.md`](tutorial/md/Ch09_FPGA.md) | iCE40 / ECP5 bitstream bring-up |
| [`Ch10_Architecture.md`](tutorial/md/Ch10_Architecture.md) | Sparkle pipeline + reference card |

The chapters are authored as plain Markdown in
`docs/tutorial/md/`.  Running
`bash tutorial-extended/build-from-md.sh` regenerates the
JupyterLab `.ipynb` notebooks (under `tutorial/notebooks/`) and
the Lake-build target (`tutorial-extended/Notebooks/Ch*.lean`).
Both are produced by xeus-lean's `xlean-convert` CLI and are
not committed to the repo.

## IP catalog — `ip-catalog/`

Documentation for the IPs (intellectual-property modules) shipped
in this repo.  See [`ip-catalog/README.md`](ip-catalog/README.md).

## Architecture — `architecture/`

How Sparkle compiles Lean to SystemVerilog and to C++ JIT, plus
the SoC- and CDC-level designs.  See
[`architecture/README.md`](architecture/README.md).

## Reference — `reference/`

Syntax reference, project setup, troubleshooting, the verification
framework, and the Sparkle ↔ Hesper equivalence work.  See
[`reference/README.md`](reference/README.md).

## Known issues — `known-issues/`

Open work items, current limitations, and benchmark snapshots.  See
[`known-issues/README.md`](known-issues/README.md).

## CHANGELOG

Append-only release notes: [`CHANGELOG.md`](CHANGELOG.md).
