# Alveo U280 — Sparkle FPGA Target (Holy Ground)

> **Status: scaffold only.** This directory exists so future work on the
> Sparkle → Alveo U280 synthesis flow has an obvious home. Nothing here
> is currently runnable — see the "What's missing" section below.

## Target hardware

- **Card**: AMD (Xilinx) Alveo U280
- **FPGA**: `xcu280-fsvh2892-2L-e` (UltraScale+, XCVU37P)
- **Memory**: 8 GiB HBM2 (2 stacks × 4 GiB, 16 pseudo-channels), 32 GiB DDR4
- **Host interface**: PCIe Gen4 × 16 via XDMA or QDMA
- **Reference docs**:
  - [UG1120 UltraScale+ Devices Integrated Block for PCIe Express](https://docs.xilinx.com/r/en-US/pg213-pcie4-uscale-plus)
  - [UG1314 Alveo U280 Data Center Accelerator Card Data Sheet](https://docs.xilinx.com/r/en-US/ds963-u280)
  - [UG1393 Vitis Application Acceleration Development Flow](https://docs.xilinx.com/r/en-US/ug1393-vitis-application-acceleration)

## Planned flow

```
  Sparkle Signal DSL (Lean)
          │
          │  #writeDesign / #synthesizeVerilog
          ▼
  SystemVerilog (verilator/generated_soc.sv and friends)
          │
          │  read_verilog + add_files (XCI for PCIe/HBM IPs)
          ▼
  Vivado synth_design -top ... -part xcu280-fsvh2892-2L-e
          │
          │  opt_design → place_design → phys_opt_design → route_design
          ▼
  .bit (standalone) or .xclbin (XRT-managed)
          │
          │  xbutil program / host XRT runtime loads
          ▼
  Running hardware on the Alveo U280 card
```

## What's present today

- **Sparkle RTL**: A complete Signal DSL SoC (picorv32 + BitNet Level-1a
  MMIO peripheral) that already generates clean, synthesizable SystemVerilog
  via `lake build IP.RV32.SoCVerilog`. The output lands in
  `verilator/generated_soc.sv` — grep it for `_gen_bitnetOut` to confirm
  the BitNet subtree is wired in.
- **Functional simulation**: Both Verilator-level (`verilator/` tree) and
  JIT-level (`lake exe rv32-flow-test`, `Tests/Integration/BitNetSoCTest.lean`)
  confirm the design behaves correctly on tiny firmware.

## What's missing (roadmap)

### Level 1b — real Vivado synthesis

- [ ] **PCIe shell**: instantiate Xilinx's XDMA Gen4 ×16 IP and wire its
      AXI-lite / AXI-MM interfaces to the Sparkle SoC's bus. Today the
      Sparkle SoC has no PCIe ingress/egress.
- [ ] **HBM controller**: instantiate 2 × Xilinx HBM IP blocks (one per
      stack) and bridge them to BitNet's weight / activation memory.
      Today BitNet's weights are burned in at Lean elaboration time;
      for a real model (dim ≥ 2048) they must live in HBM.
- [ ] **Clock wizard**: derive the SoC clock from the 100 MHz reference
      and the HBM clocks (450 MHz typical).
- [ ] **Reset synchronizer**: PCIe reset + user reset domain crossing.
- [ ] **Constraints (`constraints.xdc`)**: pin assignments for PCIe,
      HBM, USER_SI570 reference clock, and any GPIO / LEDs used for
      bring-up. See the U280 XDC template in `Xilinx/Vivado/common/data/xdc/`.
- [ ] **Vivado project (`build.tcl`)**: drive synthesis, implementation,
      and bitstream generation from Tcl so it can run headless in CI.

### Level 2 — runtime

- [ ] **Host driver (C++ + XRT)**: `xrt::bo` buffer objects for
      weight upload, `xrt::kernel::run()` for inference, DMA through
      PCIe.
- [ ] **Firmware image loader**: boot ROM that pulls the picorv32
      firmware from HBM at reset release instead of compile-time-baked.
- [ ] **Performance counters**: cycle counters and UART logging
      piped back through PCIe for host-side observability.

### Level 3 — production

- [ ] **Multi-core**: replicate the picorv32 + BitNet tile across all
      16 HBM pseudo-channels.
- [ ] **Partial reconfiguration**: load new BitNet weights without
      re-bitstreaming.
- [ ] **End-to-end benchmarks**: tokens-per-second on a real BitNet
      model vs CPU baseline.

## Files in this directory

| File | Purpose | Status |
|---|---|---|
| `README.md` | This file | ✅ |
| `build.tcl` | Vivado synthesis/P&R/bitgen script | 🚧 stub |
| `constraints.xdc` | Pin + clock + area constraints | 🚧 stub |

Everything listed as 🚧 is a commented-out placeholder showing the
intended shape. Do not try to run them until the pieces under "what's
missing" are filled in.

## Why "holy ground"?

Because every line of RTL in the Sparkle repo has been written with the
eventual goal of running on an actual FPGA card, not just simulating. This
directory is the commit point: once the flow here produces a working
`.xclbin`, Sparkle becomes a legitimate hardware tool rather than an
elegant simulator. Treat it accordingly — no shortcuts, no
fake-it-till-you-make-it, no synthetic bitstreams. When `build.tcl`
becomes runnable, it should produce a bitstream that boots the same
firmware that `lake exe bitnet-soc-test` exercises in simulation, with
identical bit-for-bit outputs.
