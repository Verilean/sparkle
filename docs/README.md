# Sparkle Documentation

Sparkle is an HDL DSL embedded in Lean 4: write hardware in Lean,
synthesise to SystemVerilog or simulate via a JIT-compiled C++
backend, and prove correctness with Lean's tactic language.  This
directory holds the documentation, organised by audience.

## Tutorial — start here

The beginner course covers Lean syntax for HDL authors,
combinational and sequential logic, modules and composition, Verilog
generation, LTL invariant proofs, equivalence checking, verified
synthesis, Yosys netlists, simulation back ends, FPGA bring-up
(iCE40 + ECP5), a tour of the compilation pipeline, and three
worked applications. The chapter list and the build instructions are in
[`tutorial/README.md`](tutorial/README.md); the chapter sources are
the Markdown files in [`tutorial/md/`](tutorial/md/).

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
| [`Ch07b_FpQuantEquivalence.md`](tutorial/md/Ch07b_FpQuantEquivalence.md) | Equivalence across number types (floating point, fixed point, quantisation) |
| [`Ch07c_VerifiedSynthesis.md`](tutorial/md/Ch07c_VerifiedSynthesis.md) | Synthesis with a proof attached (`#ved_u1`) |
| [`Ch08_Yosys.md`](tutorial/md/Ch08_Yosys.md) | Netlist generation, gate counts |
| [`Ch08b_Simulation.md`](tutorial/md/Ch08b_Simulation.md) | Three ways to simulate behind one interface |
| [`Ch08c_Silicon.md`](tutorial/md/Ch08c_Silicon.md) | From Signal to silicon: flip-flops, clocks, timing, gate count |
| [`Ch09_FPGA.md`](tutorial/md/Ch09_FPGA.md) | iCE40 / ECP5 bitstream bring-up |
| [`Ch10_Architecture.md`](tutorial/md/Ch10_Architecture.md) | Sparkle pipeline + reference card |
| [`Ch11_Web3Signer.md`](tutorial/md/Ch11_Web3Signer.md) | The web3 signing device on real hardware |
| [`Ch12_ControlPrecision.md`](tutorial/md/Ch12_ControlPrecision.md) | Control, estimation and the engineering of precision |
| [`Ch13_GpuSimulation.md`](tutorial/md/Ch13_GpuSimulation.md) | GPU simulation: Monte-Carlo sweeps and systolic arrays |
| [`Ch14_HftMarketMaking.md`](tutorial/md/Ch14_HftMarketMaking.md) | A quoting engine with a proved position bound |

The chapters are authored as plain Markdown in `docs/tutorial/md/`.
Running `bash docs/tutorial/build-from-md.sh` regenerates the
JupyterLab `.ipynb` notebooks and the Lake-build sources
(`docs/tutorial/Notebooks/Gen/`) for every chapter; `lake build
TutorialNotebooks` type-checks the code cells of chapters 0 to 12
only (13 and 14 are not imported). Both are produced by xeus-lean's
`xlean-convert` CLI and are not committed to the repo.

Older single-page tutorials remain at the top of `docs/` (see
[Single-page guides](#single-page-guides-at-the-top-of-docs)).

## Research release — `research/`

Verified synthesis: what the per-circuit proofs say, what they do
not say, how to reproduce and extend them. Start at
[`research/README.md`](research/README.md). It keeps apart the
general compiler theorem (not proved), the per-circuit proofs about
the returned intermediate representation, the SystemVerilog text
round trip, the meaning of SystemVerilog, and hardware.

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

## Single-page guides at the top of `docs/`

- [`Tutorial.md`](Tutorial.md) — the Signal DSL quick start; every
  code block is type-checked by CI (`scripts/check_tutorial.sh`).
- [`Tutorial_Extended.md`](Tutorial_Extended.md) and
  [`Tutorial_LTL.md`](Tutorial_LTL.md) — older tutorials, marked
  deprecated; replaced by chapters 4 and 6 of the course above.
- [`CudaSim.md`](CudaSim.md), [`CudaIntraSim-design.md`](CudaIntraSim-design.md)
  — the CUDA simulation back ends (batch and within-instance).
- [`SmtBridge-design.md`](SmtBridge-design.md) — design of the SMT bridge
  (untrusted finder, Lean-checked certificate).
- [`Display_Migration_Plan.md`](Display_Migration_Plan.md) — how the
  display library is split between xeus-lean and Sparkle.
- [`lean-lake-force-load-ordering-issue.md`](lean-lake-force-load-ordering-issue.md)
  — a Lean/Lake load-order problem with precompiled libraries.

## Historical VED design records

The `VED-*.md` pages at the top of `docs/` are the working notes of the
`#verify_elab_deep` / `#ved_*` development (the per-circuit proof
checker described in [`research/README.md`](research/README.md)).
They are historical records: each says at its top which branch or
commit it describes and is not kept in step with current `main`.
Several Lean files cite them by path, so they stay where they are.
For what the checker guarantees today, read the research pages, not
these.

| Topic | Records |
|---|---|
| Introduction of the entries | [`VED-MAIN-INTRO.md`](VED-MAIN-INTRO.md), [`VED-U1-MAIN.md`](VED-U1-MAIN.md) |
| Single-module circuits | [`VED-U1-PACKED.md`](VED-U1-PACKED.md), [`VED-U1-MULTISEQ.md`](VED-U1-MULTISEQ.md), [`VED-U1-WIRE-SHARE.md`](VED-U1-WIRE-SHARE.md) |
| Hierarchy (instances of sub-modules) | [`VED-HIER-DESIGN-v1.md`](VED-HIER-DESIGN-v1.md), [`VED-HIER-H2-DESIGN.md`](VED-HIER-H2-DESIGN.md), [`VED-HIER-H2A.md`](VED-HIER-H2A.md), [`VED-HIER-H2B.md`](VED-HIER-H2B.md), [`VED-HIER-H2C.md`](VED-HIER-H2C.md), [`VED-HIER-H2C-STATE.md`](VED-HIER-H2C-STATE.md), [`VED-HIER-H2D.md`](VED-HIER-H2D.md), [`VED-HIER-H2E.md`](VED-HIER-H2E.md), [`VED-HIER-H3OPEN.md`](VED-HIER-H3OPEN.md), [`VED-H3-CHILD.md`](VED-H3-CHILD.md) |
| Composition of proofs | [`VED-COMPOSITION-AXIS.md`](VED-COMPOSITION-AXIS.md), [`VED-COMPOSE-RESEARCH.md`](VED-COMPOSE-RESEARCH.md), [`VED-COMPOSE-CONNECT.md`](VED-COMPOSE-CONNECT.md) |
