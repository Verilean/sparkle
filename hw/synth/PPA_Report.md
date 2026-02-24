# Hespera PPA Report: HardwiredUnrolled vs TimeMultiplexed

## Benchmark Configuration

| Parameter | Value |
|-----------|-------|
| Layers | 12 |
| Dimension (dim) | 64 |
| FFN Dimension (ffnDim) | 64 |
| Activation Width | 32-bit Q16.16 |
| Accumulator Width | 48-bit |
| Scale Width | 32-bit Q8.24 |
| Weight Encoding | 2-bit ternary (i2_s) |
| Weights per layer | 3 x 64 = 192 (gate + up + down) |
| Total weights | 2,304 |

**Tool**: Yosys 0.62 (technology-independent synthesis with ABC)

## Area Comparison (Flattened Netlist)

| Metric | HardwiredUnrolled (HW) | TimeMultiplexed (TM) | Ratio (HW/TM) |
|--------|:----------------------:|:--------------------:|:--------------:|
| **Total Cells** | **202,566** | **99,020** | **2.05x** |
| Total Wires | 201,879 | 99,076 | 2.04x |
| Total Wire Bits | 218,594 | 99,608 | 2.19x |
| Flip-Flops | 0 | 40 | — |
| Source Lines (SV) | 19,042 | 1,909 | 9.97x |

### Cell Breakdown

| Cell Type | HW Mode | TM Mode | Ratio | Notes |
|-----------|--------:|--------:|:-----:|-------|
| `$_NAND_` | 83,021 | 35,332 | 2.35x | Main logic |
| `$_XOR_` | 52,715 | 21,133 | 2.49x | Adders / arithmetic |
| `$_AND_` | 27,119 | 11,997 | 2.26x | Logic / multipliers |
| `$_XNOR_` | 19,299 | 5,926 | 3.26x | Comparison / arithmetic |
| `$_OR_` | 8,899 | 3,218 | 2.77x | |
| `$_ANDNOT_` | 8,287 | 12,150 | 0.68x | Weight ROM muxes dominate TM |
| `$_ORNOT_` | 1,987 | 1,755 | 1.13x | |
| `$_NOR_` | 845 | 7,035 | 0.12x | Weight ROM comparison logic |
| `$_NOT_` | 106 | 315 | 0.34x | |
| `$_MUX_` | 288 | 119 | 2.42x | |
| `$_DFFE_PP0P_` | 0 | 36 | — | FSM + activation register |
| `$_DFF_PP0_` | 0 | 3 | — | State register |
| `$_DFF_PP1_` | 0 | 1 | — | State register |

## Analysis

### HW Mode Is Now 2x Larger

At dim=64 with 12 layers, the **HardwiredUnrolled mode uses 2.05x more cells** than TimeMultiplexed. This is the expected outcome at scale:

1. **Linear scaling in HW mode**: Each of the 12 layers has its own complete hardwired datapath (3 BitLinearPipelined modules + 3 ScaleMultiply + ReLUSq + ElemMul + ResidualAdd + RMSNorm). Total: 12 copies of everything.

2. **Constant core in TM mode**: Only one generic datapath is instantiated (3 DynamicBitLinear_64 + 3 ScaleMultiply + ReLUSq + ElemMul + ResidualAdd). The weight/scale ROMs add overhead but it's small compared to 12x the core.

3. **Weight ROM cost**: The TM weight ROM stores 12 layers × 3 paths × 64 weights = 2,304 ternary values as mux-tree LUTs indexed by `layer_idx`. This shows up as higher `$_ANDNOT_` and `$_NOR_` counts in TM mode, but is far less than duplicating entire datapaths.

4. **Zero-weight pruning**: HW mode prunes ~35% of weights (average ~42/64 active per path), saving some hardware. But even with pruning, 12 copies still exceed one full copy.

### Crossover Point

| Scale | HW Cells | TM Cells | Winner |
|-------|----------|----------|--------|
| dim=4, 4L | 36,605 | 40,751 | HW (0.90x) |
| **dim=64, 12L** | **202,566** | **99,020** | **TM (2.05x)** |

The crossover occurs around dim=16-32 with 4-8 layers, where the weight ROM overhead equals the savings from hardware sharing.

### Performance Trade-off

| Aspect | HardwiredUnrolled | TimeMultiplexed |
|--------|:-----------------:|:---------------:|
| Latency | 1 cycle (combinational) | N cycles (N = nLayers) |
| Throughput | Maximum | 1/N of HW |
| Area | 2.05x larger | **1x (baseline)** |
| Power | Higher (more switching) | Lower (fewer active cells) |

## Weight Distribution

Generated using LCG (seed=42) with ~1/3 probability for each of {-1, 0, +1}:

| Layer | Gate Active | Up Active | Down Active | Avg Active % |
|------:|:----------:|:---------:|:-----------:|:------------:|
| 0 | 49/64 | 41/64 | 48/64 | 71.9% |
| 1 | 48/64 | 34/64 | 41/64 | 64.1% |
| 2 | 38/64 | 46/64 | 39/64 | 64.1% |
| 3 | 38/64 | 43/64 | 46/64 | 66.1% |
| 4 | 38/64 | 42/64 | 46/64 | 65.6% |
| 5 | 40/64 | 39/64 | 40/64 | 62.0% |
| 6 | 41/64 | 43/64 | 35/64 | 62.0% |
| 7 | 40/64 | 45/64 | 39/64 | 64.6% |
| 8 | 49/64 | 43/64 | 46/64 | 71.9% |
| 9 | 41/64 | 46/64 | 38/64 | 65.1% |
| 10 | 44/64 | 44/64 | 35/64 | 64.1% |
| 11 | 40/64 | 44/64 | 43/64 | 66.1% |

Average pruning rate: ~34.6% (compared to 33.3% expected for uniform ternary).

## Synthesis Details

| Mode | ABC Time | Peak Memory | Total Time |
|------|:--------:|:-----------:|:----------:|
| HW | 84s | 2,086 MB | ~107s |
| TM | 4s | 356 MB | ~7s |

## Source Files

| File | Lines | Description |
|------|------:|-------------|
| `hw_unrolled.sv` | 19,042 | Self-contained HW mode (all sub-modules) |
| `time_muxed.sv` | 1,909 | Self-contained TM mode (all sub-modules) |
| `synth_hw.v` | — | Yosys-synthesized HW netlist |
| `synth_tm.v` | — | Yosys-synthesized TM netlist |

## Methodology

1. **Weight Generation**: Deterministic LCG (seed=42) → ternary {-1, 0, +1}
2. **RTL Generation**: Lean 4 (Sparkle HDL) → SystemVerilog (`tools/BenchmarkGen.lean`)
3. **Synthesis**: Yosys 0.62 — `proc; opt; fsm; opt; memory; opt; techmap; opt; abc; flatten; opt_clean; stat`
4. **Cell Library**: Yosys standard cells (technology-independent)
5. **Comparison**: Flattened netlist cell counts (no module boundaries)

---

*Generated by Hespera Benchmark (`lake exe benchmark-gen`)*
*Synthesis tool: Yosys 0.62*
