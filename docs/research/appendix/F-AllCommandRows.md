# Appendix F: all 327 command rows (snapshot `2bcf256b`)

[Back to the family summary](../Coverage327.md). Generated file; do not edit. Source:
[`data/coverage-327.tsv`](../data/coverage-327.tsv); generator:
[`scripts/research/coverage_table.py`](../../../scripts/research/coverage_table.py).
Regenerate with `python3 -I scripts/research/coverage_table.py`. Search this page for a file
name, a declaration or a row number (`R178`).

**What a row is.** The fixed inventory contains **327 command rows**: `#synthesizeVerilog`,
`#writeDesign` and similar commands in 136 files. They are **not 327 IPs**: one IP can own
several rows, and a row counts once however many routes prove it. A child leaf proof is never
added to its wrapper row. "Real IP" means the file lives under `IP/` or `Tests/IP/` (220 rows);
every other row is a "regression" row (107 rows: examples, tests, tutorial files).

**What "strict" means.** The original declaration, the *same run's returned IR*, the exact
statement type, only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and all
outputs. It is rung 2 of the [guarantee ladder](../README.md#the-guarantee-ladder): it says
nothing about the optimiser, the printed SystemVerilog or performance (those columns of the
ledger read "not-evaluated").

## Provenance

| Item | Value |
|---|---|
| Code SHA | `2bcf256b`: PR #163 head (branch `ved/consolidated-1`). This is the code the release contains |
| Measured SHA | `fb7124fc6620951f00e84d861da759231704b276` (`fb7124fc`), branch `meas/ved-pr16-fb71`. This is the commit the harness ran on. It is **a different commit** from the code SHA |
| Relation | `git diff --stat 2bcf256b fb7124fc` touches 27 files, all under `scripts/ved/` (the measurement harness, commit `ffea8b85`); nothing under `Sparkle/`, `Tools/`, `Tests/`, `IP/` or the lakefile. The numbers are therefore read as numbers for the code `2bcf256b`. If any later change enters the release candidate, its diff must be checked: a change of meaning or of proof generation does not inherit this coverage, only a change that leaves what a route accepts untouched (documentation, harness, CI scripts) can |
| Ledger | `pr16-fb71`, the approved ledger of the measurement at `fb7124fc`; generator `gen_ledger.py`, sha256 `6eb49c7e...` (not in this tree) |
| Inventory | pin `f694355f` (blob `4a5b801f`) |
| Toolchain | `leanprover/lean4:v4.32.1` |
| Routes | `u1`, `u1_deep`, `u1_deep_ns`, `u1_hier`, `u1_packed`, `u2_hier`, `u1_mem_packed` (7) |
| Approval | the count was approved by the project reviewer in the measurement issue (2026-11-19); the reviewer noted that the checksum list could not be re-checked independently |

The harness and the ledger generator are not part of this release tree. How to regenerate the
data from the public measurement branch is described in
[C-Reproduction.md](C-Reproduction.md); the approval records are summarised in
[D-Evidence.md](D-Evidence.md).

## Other columns, kept separate

These are **not** part of the numbers of the summary page.

| Column | Code | Result | Status |
|---|---|---|---|
| This release | code `2bcf256b`, measured at `fb7124fc` | 243 / 327 | approved ledger (reviewer, 2026-11-19) |
| Earlier baseline | `d331ff24` (an earlier VED candidate, not `main`) | 43 / 327 | approved baseline of the ledger |
| `main` before the release | `6c29b9b8` | no same-SHA row-by-row measurement in this release | that `main` had the deep route and the basic `#ved_u1` entry; it lacked the packed, hierarchy and `#ved_write_checked` entries of this snapshot. Current `main` contains them and is not measured here |

Strict rows by the proof routes that proved them (route names are the harness's):

| routes | rows |
|---|---|
| `u1` | 191 |
| `u1_packed` | 24 |
| `u1+u1_deep+u1_deep_ns` | 9 |
| `u2_hier` | 8 |
| `u1_hier+u2_hier` | 6 |
| `u1_mem_packed` | 5 |

Strict rows by provenance:

| provenance | rows |
|---|---|
| approved-earlier-sha | 42 |
| baseline-strict | 43 |
| measured-only | 158 |

## How to read the table

* **Status.** `strict`: proved on at least one route. `refused`: every route that ran refused or
  failed; the row carries **no claim**. `unmeasured`: the row could not be run on any route
  (listed separately below); it stays in the denominator.
* **Route.** For a strict row, the first route that proved it. For a refused row, the first route
  that ran; its time and memory are in the last two columns. Time and memory are those of one
  route's run (including loading imports), not of the proof alone.
* **Conditions.** The statement kind a route expected, when the ledger records one (`U2HRStmt`,
  `U2HStmt`); `-` means none recorded. The ledger of this snapshot records no non-default Lean
  options.
* **First blocker per route.** `route:cause` for each of the 7 routes, shown for refused and
  unmeasured rows. The causes are the harness's classification of the first thing that stopped
  that route. Informally: `prep` the preparation command `#verify_elab_deep` did not succeed (deep
  routes only); `table`, `multi-output`, `packed`, `hier-shape`, `shape`, `order`, `scope`,
  `conns`, `open`, `deep`, `proof` are the stage of the entry's refusal pipeline at which the
  entry refused (`VED U1 REFUSED f [stage]`); `signal` the process ended by a signal without
  recorded evidence of memory exhaustion; `external-timeout` the harness time limit; `case-error`
  Lean errors outside the checked block; `unsupported-invocation` the command form cannot be
  driven by the route; `source-missing` the row's declaration cannot be resolved at this SHA.
  The authoritative list is the pipeline in `scripts/ved/u1_gen.py` on `fb7124fc`.
* **Provenance of a strict row.** `baseline-strict`: strict already at the earlier baseline
  `d331ff24`; `approved-earlier-sha`: a reviewer-approved measurement of an earlier SHA exists;
  `measured-only`: strict in this measurement, with no separate review record of the row.

## Unmeasured rows (10)

| Row | File:line | Why |
|---|---|---|
| R69 | `Tests/Compiler/ShippingMachineFuseTest.lean:53` | `source-missing` on all routes |
| R70 | `Tests/Compiler/ShippingMachineFuseTest.lean:54` | `source-missing` on all routes |
| R71 | `Tests/Compiler/ShippingMachineFuseTest.lean:55` | `source-missing` on all routes |
| R72 | `Tests/Compiler/SimNamesTest.lean:138` | `source-missing` on all routes |
| R260 | `Tests/SymbolicParameterEmit.lean:4` | `unsupported-invocation` on all routes |
| R261 | `Tests/SymbolicParameterEmit.lean:5` | `unsupported-invocation` on all routes |
| R262 | `Tests/SymbolicParameterEmit.lean:6` | `unsupported-invocation` on all routes |
| R263 | `Tests/SymbolicParameterEmit.lean:7` | `unsupported-invocation` on all routes |
| R321 | `Tests/Tutorial/HierarchyTest.lean:68` | `unsupported-invocation` on all routes |
| R322 | `Tests/Tutorial/HierarchyTest.lean:69` | `unsupported-invocation` on all routes |

## All 327 rows

| Row | Kind | File:line | Command | Declaration | Status | Route | Conditions | First blocker per route | s | MB |
|---|---|---|---|---|---|---|---|---|---|---|
| R1 | regression | `Examples/CDC/MultiClockSim.lean:62` | `#writeDesign` | `Examples.CDC.MultiClockSim.domainACounter` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:proof; u2_hier:multi-output | 13.7 | 1627 |
| R2 | regression | `Examples/CDC/MultiClockSim.lean:94` | `#writeDesign` | `Examples.CDC.MultiClockSim.domainBAccumulator` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:proof; u2_hier:multi-output | 12.1 | 1633 |
| R3 | regression | `Examples/HierarchicalCPU.lean:110` | `#synthesizeVerilog` | `adder16` | strict | `u1` | - |  | 12.1 | 1711 |
| R4 | regression | `Examples/HierarchicalCPU.lean:117` | `#synthesizeVerilogDesign` | `registerFile2` | strict | `u1` | - |  | 12.7 | 1713 |
| R5 | regression | `Examples/HierarchicalCPU.lean:135` | `#synthesizeVerilogDesign` | `twoStageAdder` | strict | `u1` | - |  | 14.1 | 1652 |
| R6 | real-ip | `IP/Arbiter/RoundRobin.lean:79` | `#synthesizeVerilog` | `Sparkle.IP.Arbiter.RoundRobin.arbiterSignal` | strict | `u1` | - |  | 19.2 | 1746 |
| R7 | real-ip | `IP/Bus/AXI4Lite/Master.lean:139` | `#synthesizeVerilog` | `Sparkle.IP.Bus.AXI4Lite.Master.axi4LiteMaster` | strict | `u1_packed` | - |  | 34.1 | 2567 |
| R8 | real-ip | `IP/Bus/AXI4Lite/Slave.lean:135` | `#synthesizeVerilog` | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` | strict | `u1_packed` | - |  | 31.7 | 2780 |
| R9 | real-ip | `IP/Crypto/AESHW.lean:564` | `#synthesizeVerilog` | `Sparkle.IP.Crypto.AESHW.synth_aesSbox` | strict | `u1_hier+u2_hier` | - |  | 50.7 | 3381 |
| R10 | real-ip | `IP/Crypto/AESHW.lean:570` | `#synthesizeVerilog` | `Sparkle.IP.Crypto.AESHW.synth_aesRcon` | strict | `u1_hier+u2_hier` | - |  | 24.2 | 2578 |
| R11 | real-ip | `IP/RV32/Bus.lean:89` | `#synthesizeVerilog` | `Sparkle.IP.RV32.Bus.busDecoderSignal` | strict | `u1_packed` | - |  | 50.2 | 2409 |
| R12 | real-ip | `IP/RV32/CLINT.lean:111` | `#synthesizeVerilog` | `Sparkle.IP.RV32.CLINT.clintSignal` | strict | `u1_packed` | - |  | 33.2 | 3016 |
| R13 | real-ip | `IP/RV32/CSR/File.lean:179` | `#synthesizeVerilog` | `Sparkle.IP.RV32.CSR.File.csrFileSignal` | strict | `u1_packed` | - |  | 212.9 | 6932 |
| R14 | real-ip | `IP/RV32/CSR/Supervisor.lean:180` | `#synthesizeVerilog` | `Sparkle.IP.RV32.CSR.Supervisor.supervisorCsrSignal` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:proof; u2_hier:multi-output | 12.7 | 1648 |
| R15 | real-ip | `IP/RV32/Core.lean:81` | `#synthesizeVerilog` | `Sparkle.IP.RV32.aluSignal` | strict | `u1` | - |  | 21.1 | 2171 |
| R16 | real-ip | `IP/RV32/Core.lean:119` | `#synthesizeVerilog` | `Sparkle.IP.RV32.branchCompSignal` | strict | `u1` | - |  | 18.1 | 1852 |
| R17 | real-ip | `IP/RV32/Core.lean:143` | `#synthesizeVerilog` | `Sparkle.IP.RV32.hazardSignal` | strict | `u1` | - |  | 19.6 | 2892 |
| R18 | real-ip | `IP/RV32/Core.lean:168` | `#synthesizeVerilog` | `Sparkle.IP.RV32.decoderFieldsSignal` | strict | `u1_packed` | - |  | 15.6 | 1728 |
| R19 | real-ip | `IP/RV32/Core.lean:249` | `#synthesizeVerilog` | `Sparkle.IP.RV32.immGenSignal` | strict | `u1` | - |  | 33.1 | 2276 |
| R20 | real-ip | `IP/RV32/Core.lean:315` | `#synthesizeVerilog` | `Sparkle.IP.RV32.aluControlSignal` | strict | `u1` | - |  | 27.7 | 2229 |
| R21 | real-ip | `IP/RV32/Core.lean:377` | `#synthesizeVerilog` | `Sparkle.IP.RV32.controlSignalsSignal` | strict | `u1_packed` | - |  | 27.6 | 2086 |
| R22 | real-ip | `IP/RV32/Divider.lean:262` | `#synthesizeVerilog` | `Sparkle.IP.RV32.Divider.dividerSignal` | strict | `u1_packed` | - |  | 95.2 | 3828 |
| R23 | real-ip | `IP/RV32/MMU/Top.lean:396` | `#synthesizeVerilog` | `Sparkle.IP.RV32.MMU.mmuTopSignal` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:proof; u2_hier:multi-output | 12.6 | 1676 |
| R24 | real-ip | `IP/RV32/Pipeline.lean:312` | `#synthesizeVerilog` | `Sparkle.IP.RV32.rv32iCore` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 17.1 | 1705 |
| R25 | real-ip | `IP/RV32/SoCVerilog.lean:80` | `#writeDesign` | `Sparkle.IP.RV32.SoCVerilog.rv32iSoCSynth` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:shape; u2_hier:multi-output | 15.7 | 1842 |
| R26 | real-ip | `IP/RV32/Trap.lean:134` | `#synthesizeVerilog` | `Sparkle.IP.RV32.Trap.trapDelegSignal` | strict | `u1_packed` | - |  | 54.6 | 2856 |
| R27 | real-ip | `IP/RV32/UART.lean:101` | `#synthesizeVerilog` | `Sparkle.IP.RV32.UART.uartSignal` | strict | `u1_packed` | - |  | 21.1 | 2438 |
| R28 | real-ip | `IP/Video/H264/CAVLCSynth.lean:799` | `#writeDesign` | `Sparkle.IP.Video.H264.CAVLCSynth.cavlcSynthModule` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:signal; u1_packed:shape; u2_hier:multi-output | 14.6 | 1790 |
| R29 | real-ip | `IP/Video/H264/DecoderSynth.lean:370` | `#writeDesign` | `Sparkle.IP.Video.H264.DecoderSynth.decoderPipeline` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:proof; u1_packed:shape; u2_hier:multi-output | 13.8 | 1759 |
| R30 | real-ip | `IP/Video/H264/DequantSynth.lean:216` | `#writeDesign` | `Sparkle.IP.Video.H264.DequantSynth.dequantModule` | strict | `u1_mem_packed` | - |  | 148.3 | 3428 |
| R31 | real-ip | `IP/Video/H264/EncoderSynth.lean:355` | `#writeDesign` | `Sparkle.IP.Video.H264.EncoderSynth.encoderPipeline` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:proof; u1_packed:shape; u2_hier:multi-output | 14.7 | 1763 |
| R32 | real-ip | `IP/Video/H264/ForwardDCTSynth.lean:239` | `#writeDesign` | `Sparkle.IP.Video.H264.ForwardDCTSynth.fwdDCTModule` | strict | `u1_mem_packed` | - |  | 329.5 | 6444 |
| R33 | real-ip | `IP/Video/H264/FrameEncoderSynth.lean:37` | `#writeDesign` | `Sparkle.IP.Video.H264.FrameEncoder.h264FrameEncoder` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:shape; u2_hier:multi-output | 15.8 | 1792 |
| R34 | real-ip | `IP/Video/H264/IDCTSynth.lean:269` | `#writeDesign` | `Sparkle.IP.Video.H264.IDCTSynth.idctModule` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:proof; u1_packed:shape; u2_hier:multi-output | 13.7 | 1756 |
| R35 | real-ip | `IP/Video/H264/MP4EncoderSynth.lean:34` | `#writeDesign` | `Sparkle.IP.Video.H264.MP4Encoder.h264MP4Encoder` | refused | `u1` | - | u1:multi-output; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:shape; u2_hier:multi-output | 16.1 | 1793 |
| R36 | real-ip | `IP/Video/H264/NALSynth.lean:187` | `#writeDesign` | `Sparkle.IP.Video.H264.NALSynth.nalStreamModule` | strict | `u1_packed` | - |  | 82.7 | 4085 |
| R37 | real-ip | `IP/Video/H264/QuantRoundtripSynth.lean:159` | `#writeDesign` | `Sparkle.IP.Video.H264.QuantRoundtripSynth.quantDequantSynth` | strict | `u1_mem_packed` | - |  | 58.2 | 2690 |
| R38 | real-ip | `IP/Video/H264/QuantSynth.lean:209` | `#writeDesign` | `Sparkle.IP.Video.H264.QuantSynth.quantModule` | strict | `u1_mem_packed` | - |  | 277.9 | 5045 |
| R39 | real-ip | `IP/Video/H264/ReconstructSynth.lean:162` | `#writeDesign` | `Sparkle.IP.Video.H264.ReconstructSynth.reconstructModule` | strict | `u1_mem_packed` | - |  | 94.2 | 2956 |
| R40 | real-ip | `IP/YOLOv8/ActivationBuffer.lean:52` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.ActivationBuffer.activationDoubleBuffer` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 14.2 | 1634 |
| R41 | real-ip | `IP/YOLOv8/Backbone.lean:202` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Backbone.backboneController` | strict | `u1_packed` | - |  | 71.3 | 3202 |
| R42 | real-ip | `IP/YOLOv8/Blocks/Bottleneck.lean:129` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController` | strict | `u1_packed` | - |  | 22.1 | 1958 |
| R43 | real-ip | `IP/YOLOv8/Blocks/C2f.lean:148` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Blocks.C2f.c2fController` | strict | `u1_packed` | - |  | 30.1 | 2190 |
| R44 | real-ip | `IP/YOLOv8/Blocks/ConvBnSiLU.lean:68` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Blocks.ConvBnSiLU.convBnSiLU` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:signal; u2_hier:multi-output | 13.2 | 1651 |
| R45 | real-ip | `IP/YOLOv8/Blocks/SPPF.lean:130` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Blocks.SPPF.sppfController` | strict | `u1_packed` | - |  | 25.6 | 2148 |
| R46 | real-ip | `IP/YOLOv8/Head.lean:167` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Head.headController` | strict | `u1_packed` | - |  | 49.6 | 2697 |
| R47 | real-ip | `IP/YOLOv8/Neck.lean:165` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Neck.neckController` | strict | `u1_packed` | - |  | 106.8 | 3227 |
| R48 | real-ip | `IP/YOLOv8/Primitives/Activation.lean:35` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Primitives.Activation.relu` | strict | `u1` | - |  | 12.6 | 1723 |
| R49 | real-ip | `IP/YOLOv8/Primitives/Conv2DEngine.lean:159` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Primitives.Conv2DEngine.conv2DEngine` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:multi-output; u1_mem_packed:shape; u1_packed:external-timeout; u2_hier:multi-output | 13.1 | 1651 |
| R50 | real-ip | `IP/YOLOv8/Primitives/Dequant.lean:65` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Primitives.Dequant.dequantPacked` | strict | `u1_packed` | - |  | 25.2 | 2133 |
| R51 | real-ip | `IP/YOLOv8/Primitives/MaxPool.lean:49` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Primitives.MaxPool.maxPool2x2` | strict | `u1` | - |  | 15.3 | 1675 |
| R52 | real-ip | `IP/YOLOv8/Primitives/Requantize.lean:69` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize` | strict | `u1` | - |  | 17.8 | 1854 |
| R53 | real-ip | `IP/YOLOv8/Primitives/Upsample.lean:93` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Primitives.Upsample.upsample2x` | strict | `u1_packed` | - |  | 17.5 | 1893 |
| R54 | real-ip | `IP/YOLOv8/TextEmbedding.lean:107` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.TextEmbedding.dotProductEngine` | strict | `u1_packed` | - |  | 27.7 | 2565 |
| R55 | real-ip | `IP/YOLOv8/Top.lean:171` | `#synthesizeVerilog` | `Sparkle.IP.YOLOv8.Top.yolov8nTop` | strict | `u1_packed` | - |  | 65.2 | 3236 |
| R56 | regression | `Tests/CircuitDoTest.lean:181` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.counterCdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 14.1 | 1684 |
| R57 | regression | `Tests/CircuitDoTest.lean:182` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.resetCounterCdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 14.2 | 1687 |
| R58 | regression | `Tests/CircuitDoTest.lean:183` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.twoRegResetCdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 16.2 | 1761 |
| R59 | regression | `Tests/CircuitDoTest.lean:184` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.heldRegCdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 15.1 | 1788 |
| R60 | regression | `Tests/CircuitDoTest.lean:185` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.fsm3Cdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 14.1 | 1734 |
| R61 | regression | `Tests/CircuitDoTest.lean:186` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.fsmHoldCdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 16.2 | 1855 |
| R62 | regression | `Tests/CircuitDoTest.lean:187` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.fourCounterCdo` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 18.2 | 1935 |
| R63 | regression | `Tests/CircuitDoTest.lean:192` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.pairCounterCdo` | refused | `u1` | - | u1:multi-output; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 13.2 | 1650 |
| R64 | regression | `Tests/CircuitDoTest.lean:193` | `#synthesizeVerilog` | `Sparkle.Tests.CircuitDoTest.pairRecordCdo` | refused | `u1` | - | u1:multi-output; u1_deep:table; u1_deep_ns:table; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 12.7 | 1642 |
| R65 | regression | `Tests/Compiler/MultiInstanceTest.lean:175` | `#synthesizeVerilog` | `Sparkle.Tests.Compiler.MultiInstance.mesh2x2` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 12.7 | 1651 |
| R66 | regression | `Tests/Compiler/MultiOutputSubModuleHangRepro.lean:80` | `#synthesizeVerilog` | `Sparkle.Tests.Compiler.MultiOutputSubModuleHangRepro.baselineNoSubmodule` | strict | `u1` | - |  | 14.1 | 1713 |
| R67 | regression | `Tests/Compiler/MultiOutputSubModuleHangRepro.lean:103` | `#synthesizeVerilog` | `Sparkle.Tests.Compiler.MultiOutputSubModuleHangRepro.baselineKvHw1Reg` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 11.6 | 1642 |
| R68 | regression | `Tests/Compiler/MultiOutputSubModuleHangRepro.lean:154` | `#synthesizeVerilog` | `Sparkle.Tests.Compiler.MultiOutputSubModuleHangRepro.reproKvHw2Reg` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 12.7 | 1654 |
| R69 | regression | `Tests/Compiler/ShippingMachineFuseTest.lean:53` | `#synthesizeVerilog` |  | unmeasured |  | - | u1:source-missing; u1_deep:source-missing; u1_deep_ns:source-missing; u1_hier:source-missing; u1_mem_packed:source-missing; u1_packed:source-missing; u2_hier:source-missing |  |  |
| R70 | regression | `Tests/Compiler/ShippingMachineFuseTest.lean:54` | `#synthesizeVerilog` |  | unmeasured |  | - | u1:source-missing; u1_deep:source-missing; u1_deep_ns:source-missing; u1_hier:source-missing; u1_mem_packed:source-missing; u1_packed:source-missing; u2_hier:source-missing |  |  |
| R71 | regression | `Tests/Compiler/ShippingMachineFuseTest.lean:55` | `#synthesizeVerilog` |  | unmeasured |  | - | u1:source-missing; u1_deep:source-missing; u1_deep_ns:source-missing; u1_hier:source-missing; u1_mem_packed:source-missing; u1_packed:source-missing; u2_hier:source-missing |  |  |
| R72 | regression | `Tests/Compiler/SimNamesTest.lean:138` | `#writeDesign` |  | unmeasured |  | - | u1:source-missing; u1_deep:source-missing; u1_deep_ns:source-missing; u1_hier:source-missing; u1_mem_packed:source-missing; u1_packed:source-missing; u2_hier:source-missing |  |  |
| R73 | regression | `Tests/CompilerTests.lean:31` | `#synthesizeVerilog` | `Tests.CompilerTests.testComplement8` | strict | `u1` | - |  | 12.7 | 1673 |
| R74 | regression | `Tests/CompilerTests.lean:39` | `#synthesizeVerilog` | `Tests.CompilerTests.testComplement32` | strict | `u1` | - |  | 12.1 | 1677 |
| R75 | regression | `Tests/CompilerTests.lean:51` | `#synthesizeVerilog` | `Tests.CompilerTests.testLambdaConcat` | strict | `u1` | - |  | 12.7 | 1712 |
| R76 | regression | `Tests/CompilerTests.lean:59` | `#synthesizeVerilog` | `Tests.CompilerTests.testLambdaAddConst` | strict | `u1` | - |  | 12.2 | 1663 |
| R77 | regression | `Tests/CompilerTests.lean:72` | `#synthesizeVerilog` | `Tests.CompilerTests.testHwLet2` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 11.6 | 1631 |
| R78 | regression | `Tests/CompilerTests.lean:81` | `#synthesizeVerilog` | `Tests.CompilerTests.testHwLet3` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 11.6 | 1635 |
| R79 | real-ip | `Tests/IP/Bus/CANHWTest.lean:97` | `#synthesizeVerilog` | `synth_canCrc15` | strict | `u1` | - |  | 16.7 | 1846 |
| R80 | real-ip | `Tests/IP/Bus/CANopenHWTest.lean:123` | `#synthesizeVerilog` | `synth_canopenFc` | strict | `u1` | - |  | 12.6 | 1672 |
| R81 | real-ip | `Tests/IP/Bus/CANopenHWTest.lean:130` | `#synthesizeVerilog` | `synth_canopenIsNmt` | strict | `u1` | - |  | 12.6 | 1746 |
| R82 | real-ip | `Tests/IP/Bus/CANopenHWTest.lean:139` | `#synthesizeVerilog` | `synth_canopenNmtState` | strict | `u1` | - |  | 17.6 | 1840 |
| R83 | real-ip | `Tests/IP/Bus/CRSFHWTest.lean:93` | `#synthesizeVerilog` | `synth_crsfCrc8` | strict | `u1` | - |  | 70.7 | 3049 |
| R84 | real-ip | `Tests/IP/Bus/DroneCANHWTest.lean:106` | `#synthesizeVerilog` | `synth_droneCanCrc16` | strict | `u1` | - |  | 83.8 | 3492 |
| R85 | real-ip | `Tests/IP/Bus/DroneCANHWTest.lean:113` | `#synthesizeVerilog` | `synth_droneCanNodeFilter` | strict | `u1` | - |  | 16.1 | 2215 |
| R86 | real-ip | `Tests/IP/Bus/DroneCANHWTest.lean:121` | `#synthesizeVerilog` | `synth_droneCanTidError` | strict | `u1` | - |  | 23.6 | 1971 |
| R87 | real-ip | `Tests/IP/Bus/I2CHWTest.lean:79` | `#synthesizeVerilog` | `synth_i2cMasterState` | strict | `u1` | - |  | 54.2 | 4164 |
| R88 | real-ip | `Tests/IP/Bus/LINHWTest.lean:86` | `#synthesizeVerilog` | `synth_linPidParity` | strict | `u1` | - |  | 16.6 | 1917 |
| R89 | real-ip | `Tests/IP/Bus/LINHWTest.lean:95` | `#synthesizeVerilog` | `synth_linChecksum` | strict | `u1` | - |  | 16.2 | 1931 |
| R90 | real-ip | `Tests/IP/Bus/MIL1553HWTest.lean:93` | `#synthesizeVerilog` | `synth_mil1553Parity` | strict | `u1` | - |  | 115.7 | 2804 |
| R91 | real-ip | `Tests/IP/Bus/MIL1553HWTest.lean:100` | `#synthesizeVerilog` | `synth_mil1553Manchester` | strict | `u1` | - |  | 13.7 | 1716 |
| R92 | real-ip | `Tests/IP/Bus/PCIeHFTTest.lean:97` | `#synthesizeVerilog` | `synth_hftPcieOutByte` | strict | `u2_hier` | U2HRStmt registers=true |  | 751.5 | 17319 |
| R93 | real-ip | `Tests/IP/Bus/PCIeHFTTest.lean:107` | `#synthesizeVerilog` | `synth_hftPciePulse` | strict | `u1` | - |  | 148.3 | 7245 |
| R94 | real-ip | `Tests/IP/Bus/PCIeTest.lean:135` | `#synthesizeVerilog` | `synth_tlpHeaderByte` | strict | `u2_hier` | U2HStmt registers=false |  | 22.2 | 2152 |
| R95 | real-ip | `Tests/IP/Bus/PCIeTest.lean:143` | `#synthesizeVerilog` | `synth_tlpRxAddr` | strict | `u1` | - |  | 36.7 | 2601 |
| R96 | real-ip | `Tests/IP/Bus/PCIeTest.lean:151` | `#synthesizeVerilog` | `synth_tlpRxIsWrite` | strict | `u1` | - |  | 35.2 | 2608 |
| R97 | real-ip | `Tests/IP/Bus/SBUSHWTest.lean:98` | `#synthesizeVerilog` | `synth_sbusIdx` | strict | `u1` | - |  | 22.7 | 2009 |
| R98 | real-ip | `Tests/IP/Bus/SBUSHWTest.lean:107` | `#synthesizeVerilog` | `synth_sbusCh0` | strict | `u1` | - |  | 24.6 | 2113 |
| R99 | real-ip | `Tests/IP/Bus/SPIHWTest.lean:86` | `#synthesizeVerilog` | `synth_spiSclk` | strict | `u1` | - |  | 61.1 | 3502 |
| R100 | real-ip | `Tests/IP/Bus/SPIHWTest.lean:98` | `#synthesizeVerilog` | `synth_spiMisoByte` | strict | `u1` | - |  | 60.1 | 3469 |
| R101 | real-ip | `Tests/IP/Control/IIRBiquadTest.lean:94` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.IIRBiquadTest.stableTop` | strict | `u1` | - |  | 367.5 | 7368 |
| R102 | real-ip | `Tests/IP/Control/IIRBiquadTest.lean:95` | `#synthesizeVerilog` |  | refused | `u1` | - | u1:signal; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 543.2 | 1069 |
| R103 | real-ip | `Tests/IP/Control/LQRTest.lean:102` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.LQRTest.lqrLoopTop` | strict | `u1` | - |  | 243.4 | 4249 |
| R104 | real-ip | `Tests/IP/Control/LQRTest.lean:103` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.LQRTest.lqrCtrlTop` | strict | `u1` | - |  | 22.2 | 2113 |
| R105 | real-ip | `Tests/IP/Control/ObserverTest.lean:257` | `#synthesizeVerilog` |  | refused | `u1` | - | u1:external-timeout; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 900.1 | 59 |
| R106 | real-ip | `Tests/IP/Control/ObserverTest.lean:258` | `#synthesizeVerilog` |  | refused | `u1` | - | u1:external-timeout; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 900.1 | 56 |
| R107 | real-ip | `Tests/IP/Control/ObserverTest.lean:259` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.ObserverTest.dividerTop` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 41.8 | 3807 |
| R108 | real-ip | `Tests/IP/Control/ObserverTest.lean:260` | `#synthesizeVerilog` |  | refused | `u1` | - | u1:signal; u1_deep:signal; u1_deep_ns:signal; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 86.7 | 81 |
| R109 | real-ip | `Tests/IP/Control/PIDTest.lean:103` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PIDTest.pidTop` | strict | `u1` | - |  | 281.4 | 5142 |
| R110 | real-ip | `Tests/IP/Control/PIDTest.lean:104` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PIDTest.pidLoopTop` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 94.8 | 8449 |
| R111 | real-ip | `Tests/IP/Control/PrecisionSweepTest.lean:361` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PrecisionSweepTest.sweepQ7_8` | strict | `u1` | - |  | 442.2 | 9133 |
| R112 | real-ip | `Tests/IP/Control/PrecisionSweepTest.lean:362` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PrecisionSweepTest.sweepQ15_16` | strict | `u1` | - |  | 364.6 | 7094 |
| R113 | real-ip | `Tests/IP/Control/PrecisionSweepTest.lean:363` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PrecisionSweepTest.sweepQ23_8` | strict | `u1` | - |  | 334.0 | 6186 |
| R114 | real-ip | `Tests/IP/Control/PrecisionSweepTest.lean:364` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PrecisionSweepTest.sweepMarginalQ7_8` | strict | `u1` | - |  | 411.2 | 11164 |
| R115 | real-ip | `Tests/IP/Control/PrecisionSweepTest.lean:365` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Control.PrecisionSweepTest.sweepMarginalQ15_16` | strict | `u1` | - |  | 365.5 | 9248 |
| R116 | real-ip | `Tests/IP/Crypto/AESGCMHWTest.lean:161` | `#synthesizeVerilog` | `synth_gcmCounter` | strict | `u1` | - |  | 13.7 | 1730 |
| R117 | real-ip | `Tests/IP/Crypto/AESGCMHWTest.lean:169` | `#synthesizeVerilog` | `synth_gcmTagY` | strict | `u1` | - |  | 16.2 | 1781 |
| R118 | real-ip | `Tests/IP/Crypto/AESGCMHWTest.lean:177` | `#synthesizeVerilog` | `synth_gcmTagFire` | strict | `u1` | - |  | 16.1 | 1812 |
| R119 | real-ip | `Tests/IP/Crypto/BIP32CKDHWTest.lean:94` | `#synthesizeVerilog` | `synth_ckd_childKey` | strict | `u1` | - |  | 67.2 | 4131 |
| R120 | real-ip | `Tests/IP/Crypto/BIP32CKDHWTest.lean:103` | `#synthesizeVerilog` | `synth_ckd_cc0` | strict | `u1` | - |  | 61.2 | 3704 |
| R121 | real-ip | `Tests/IP/Crypto/BIP32CKDHWTest.lean:112` | `#synthesizeVerilog` | `synth_ckd_done` | strict | `u1` | - |  | 70.3 | 4023 |
| R122 | real-ip | `Tests/IP/Crypto/BIP32CKDHWTest.lean:121` | `#synthesizeVerilog` | `synth_ckd_blkStart` | strict | `u1` | - |  | 68.2 | 3729 |
| R123 | real-ip | `Tests/IP/Crypto/BLS12MillerHWTest.lean:48` | `#synthesizeVerilog` | `synth_millerStep_fNum` | strict | `u1` | - |  | 33.2 | 2599 |
| R124 | real-ip | `Tests/IP/Crypto/BLS12MillerHWTest.lean:58` | `#synthesizeVerilog` | `synth_millerStep_done` | strict | `u1` | - |  | 37.2 | 3028 |
| R125 | real-ip | `Tests/IP/Crypto/BLS12MillerHWTest.lean:68` | `#synthesizeVerilog` | `synth_millerStep_f12start` | strict | `u1` | - |  | 35.2 | 2862 |
| R126 | real-ip | `Tests/IP/Crypto/EcdsaSignDemoTest.lean:105` | `#synthesizeVerilog` | `synth_signCore` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 24.7 | 1662 |
| R127 | real-ip | `Tests/IP/Crypto/EcdsaSignDemoTest.lean:117` | `#synthesizeVerilog` | `synth_demoTx` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 20.9 | 1663 |
| R128 | real-ip | `Tests/IP/Crypto/Ed25519FieldHWTest.lean:89` | `#synthesizeVerilog` | `synth_ed25519MulResult` | strict | `u1` | - |  | 35.2 | 2681 |
| R129 | real-ip | `Tests/IP/Crypto/Ed25519FieldHWTest.lean:97` | `#synthesizeVerilog` | `synth_ed25519MulDone` | strict | `u1` | - |  | 36.3 | 2544 |
| R130 | real-ip | `Tests/IP/Crypto/Ed25519PointOpHWTest.lean:135` | `#synthesizeVerilog` | `synth_ed25519PointOpX` | strict | `u1` | - |  | 210.0 | 7449 |
| R131 | real-ip | `Tests/IP/Crypto/Ed25519PointOpHWTest.lean:144` | `#synthesizeVerilog` | `synth_ed25519PointOpDone` | strict | `u1` | - |  | 210.5 | 7498 |
| R132 | real-ip | `Tests/IP/Crypto/Ed25519ScalarMulHWTest.lean:68` | `#synthesizeVerilog` | `synth_ed25519ScalarMulX` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 116.3 | 5104 |
| R133 | real-ip | `Tests/IP/Crypto/Ed25519ScalarMulHWTest.lean:77` | `#synthesizeVerilog` | `synth_ed25519ScalarMulDone` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 122.9 | 4838 |
| R134 | real-ip | `Tests/IP/Crypto/Ed25519SignHWTest.lean:67` | `#synthesizeVerilog` | `synth_ed25519SignS` | strict | `u1` | - |  | 20.7 | 2168 |
| R135 | real-ip | `Tests/IP/Crypto/Ed25519SignHWTest.lean:75` | `#synthesizeVerilog` | `synth_ed25519SignDone` | strict | `u1` | - |  | 22.6 | 2212 |
| R136 | real-ip | `Tests/IP/Crypto/Eip1559EnvelopeHWTest.lean:95` | `#synthesizeVerilog` | `synth_envByte` | strict | `u1` | - |  | 44.1 | 3393 |
| R137 | real-ip | `Tests/IP/Crypto/Eip1559EnvelopeHWTest.lean:103` | `#synthesizeVerilog` | `synth_envValid` | strict | `u1` | - |  | 31.1 | 2615 |
| R138 | real-ip | `Tests/IP/Crypto/Eip1559EnvelopeHWTest.lean:111` | `#synthesizeVerilog` | `synth_envDone` | strict | `u1` | - |  | 29.2 | 2489 |
| R139 | real-ip | `Tests/IP/Crypto/Fp12MulHWTest.lean:112` | `#synthesizeVerilog` | `synth_fp12MulC00a` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 444.3 | 20625 |
| R140 | real-ip | `Tests/IP/Crypto/Fp12MulHWTest.lean:127` | `#synthesizeVerilog` | `synth_fp12MulDone` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 624.4 | 20524 |
| R141 | real-ip | `Tests/IP/Crypto/Fp2MulHWTest.lean:100` | `#synthesizeVerilog` | `synth_fp2MulC0` | strict | `u1` | - |  | 78.2 | 3900 |
| R142 | real-ip | `Tests/IP/Crypto/Fp2MulHWTest.lean:110` | `#synthesizeVerilog` | `synth_fp2MulC1` | strict | `u1` | - |  | 102.3 | 4247 |
| R143 | real-ip | `Tests/IP/Crypto/Fp2MulHWTest.lean:120` | `#synthesizeVerilog` | `synth_fp2MulDone` | strict | `u1` | - |  | 40.6 | 2988 |
| R144 | real-ip | `Tests/IP/Crypto/Fp381MontMulHWTest.lean:112` | `#synthesizeVerilog` | `synth_fp381MontMulResult` | strict | `u1` | - |  | 31.2 | 3088 |
| R145 | real-ip | `Tests/IP/Crypto/Fp381MontMulHWTest.lean:120` | `#synthesizeVerilog` | `synth_fp381MontMulDone` | strict | `u1` | - |  | 30.1 | 2547 |
| R146 | real-ip | `Tests/IP/Crypto/Fp6MulHWTest.lean:104` | `#synthesizeVerilog` | `synth_fp6MulC0a` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 210.9 | 12772 |
| R147 | real-ip | `Tests/IP/Crypto/Fp6MulHWTest.lean:115` | `#synthesizeVerilog` | `synth_fp6MulDone` | strict | `u1` | - |  | 243.9 | 9492 |
| R148 | real-ip | `Tests/IP/Crypto/G2PointOpHWTest.lean:168` | `#synthesizeVerilog` |  | refused | `u1` | - | u1:signal; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 247.4 | 1068 |
| R149 | real-ip | `Tests/IP/Crypto/G2ScalarMulHWTest.lean:106` | `#synthesizeVerilog` | `synth_g2ScalarMul_x0` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 277.0 | 8361 |
| R150 | real-ip | `Tests/IP/Crypto/G2ScalarMulHWTest.lean:115` | `#synthesizeVerilog` | `synth_g2ScalarMul_done` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 303.5 | 9833 |
| R151 | real-ip | `Tests/IP/Crypto/GHASHHWSynth.lean:18` | `#synthesizeVerilog` | `synth_gmulHWResult` | strict | `u1` | - |  | 29.6 | 2984 |
| R152 | real-ip | `Tests/IP/Crypto/GHASHHWSynth.lean:26` | `#synthesizeVerilog` | `synth_gmulHWDone` | strict | `u1` | - |  | 29.9 | 2550 |
| R153 | real-ip | `Tests/IP/Crypto/GoldilocksHWTest.lean:90` | `#synthesizeVerilog` | `synth_goldilocksMulResult` | strict | `u1` | - |  | 33.2 | 2476 |
| R154 | real-ip | `Tests/IP/Crypto/GoldilocksHWTest.lean:98` | `#synthesizeVerilog` | `synth_goldilocksMulDone` | strict | `u1` | - |  | 32.6 | 2563 |
| R155 | real-ip | `Tests/IP/Crypto/HKDFHWTest.lean:170` | `#synthesizeVerilog` | `synth_hkdfCounter` | strict | `u1` | - |  | 24.2 | 2193 |
| R156 | real-ip | `Tests/IP/Crypto/HKDFHWTest.lean:180` | `#synthesizeVerilog` | `synth_hkdfDone` | strict | `u1` | - |  | 24.1 | 2273 |
| R157 | real-ip | `Tests/IP/Crypto/HKDFHWTest.lean:190` | `#synthesizeVerilog` | `synth_hkdfTrig` | strict | `u1` | - |  | 26.1 | 2520 |
| R158 | real-ip | `Tests/IP/Crypto/HMACSHA512HWTest.lean:109` | `#synthesizeVerilog` | `synth_hmac_out0` | strict | `u1` | - |  | 56.2 | 3561 |
| R159 | real-ip | `Tests/IP/Crypto/HMACSHA512HWTest.lean:118` | `#synthesizeVerilog` | `synth_hmac_blkStart` | strict | `u1` | - |  | 58.2 | 3954 |
| R160 | real-ip | `Tests/IP/Crypto/HMACSHA512HWTest.lean:127` | `#synthesizeVerilog` | `synth_hmac_bWin15` | strict | `u1` | - |  | 68.2 | 4189 |
| R161 | real-ip | `Tests/IP/Crypto/HMACSHA512HWTest.lean:136` | `#synthesizeVerilog` | `synth_hmac_done` | strict | `u1` | - |  | 68.2 | 3830 |
| R162 | real-ip | `Tests/IP/Crypto/Keccak256HWTest.lean:112` | `#synthesizeVerilog` | `synth_keccakRc` | strict | `u1_hier+u2_hier` | - |  | 75.7 | 5241 |
| R163 | real-ip | `Tests/IP/Crypto/Keccak256SpongeTest.lean:151` | `#synthesizeVerilog` | `synth_spongeD0` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 38.7 | 1703 |
| R164 | real-ip | `Tests/IP/Crypto/Keccak256SpongeTest.lean:165` | `#synthesizeVerilog` | `synth_spongeDone` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 40.2 | 1702 |
| R165 | real-ip | `Tests/IP/Crypto/MerkleHWTest.lean:167` | `#synthesizeVerilog` | `synth_merkleSlot0` | strict | `u1` | - |  | 257.9 | 5117 |
| R166 | real-ip | `Tests/IP/Crypto/MerkleHWTest.lean:176` | `#synthesizeVerilog` | `synth_merkleOcc` | strict | `u1` | - |  | 254.9 | 5177 |
| R167 | real-ip | `Tests/IP/Crypto/MerkleHWTest.lean:185` | `#synthesizeVerilog` | `synth_merkleCombineReq` | strict | `u1` | - |  | 274.9 | 5290 |
| R168 | real-ip | `Tests/IP/Crypto/ModInvHWTest.lean:115` | `#synthesizeVerilog` | `synth_modInvResult` | strict | `u1` | - |  | 32.6 | 2553 |
| R169 | real-ip | `Tests/IP/Crypto/ModInvHWTest.lean:125` | `#synthesizeVerilog` | `synth_modInvDone` | strict | `u1` | - |  | 33.7 | 2613 |
| R170 | real-ip | `Tests/IP/Crypto/ModInvHWTest.lean:135` | `#synthesizeVerilog` | `synth_modInvMulStart` | strict | `u1` | - |  | 33.6 | 2739 |
| R171 | real-ip | `Tests/IP/Crypto/P256ECDSAHWTest.lean:128` | `#synthesizeVerilog` | `synth_ecdsaR` | strict | `u1` | - |  | 153.8 | 5679 |
| R172 | real-ip | `Tests/IP/Crypto/P256ECDSAHWTest.lean:142` | `#synthesizeVerilog` | `synth_ecdsaS` | strict | `u1` | - |  | 156.8 | 6394 |
| R173 | real-ip | `Tests/IP/Crypto/P256ECDSAHWTest.lean:156` | `#synthesizeVerilog` | `synth_ecdsaDone` | strict | `u1` | - |  | 153.3 | 5877 |
| R174 | real-ip | `Tests/IP/Crypto/P256FieldHWTest.lean:89` | `#synthesizeVerilog` | `synth_p256MulResult` | strict | `u1` | - |  | 30.6 | 2497 |
| R175 | real-ip | `Tests/IP/Crypto/P256FieldHWTest.lean:97` | `#synthesizeVerilog` | `synth_p256MulDone` | strict | `u1` | - |  | 31.1 | 2782 |
| R176 | real-ip | `Tests/IP/Crypto/P256OrderHWTest.lean:89` | `#synthesizeVerilog` | `synth_p256OrderMulResult` | strict | `u1` | - |  | 30.7 | 2986 |
| R177 | real-ip | `Tests/IP/Crypto/P256OrderHWTest.lean:97` | `#synthesizeVerilog` | `synth_p256OrderMulDone` | strict | `u1` | - |  | 31.1 | 2571 |
| R178 | real-ip | `Tests/IP/Crypto/P256PointOpHWTest.lean:147` | `#synthesizeVerilog` | `synth_p256PointOpX` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 245.4 | 15803 |
| R179 | real-ip | `Tests/IP/Crypto/P256PointOpHWTest.lean:158` | `#synthesizeVerilog` | `synth_p256PointOpDone` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 311.3 | 11597 |
| R180 | real-ip | `Tests/IP/Crypto/P256PointOpHWTest.lean:169` | `#synthesizeVerilog` | `synth_p256PointOpMulStart` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 280.3 | 9806 |
| R181 | real-ip | `Tests/IP/Crypto/P256ScalarMulHWTest.lean:135` | `#synthesizeVerilog` | `synth_p256ScalarMulX` | strict | `u1` | - |  | 108.7 | 5547 |
| R182 | real-ip | `Tests/IP/Crypto/P256ScalarMulHWTest.lean:146` | `#synthesizeVerilog` | `synth_p256ScalarMulDone` | strict | `u1` | - |  | 112.7 | 5898 |
| R183 | real-ip | `Tests/IP/Crypto/P256ScalarMulHWTest.lean:157` | `#synthesizeVerilog` | `synth_p256ScalarMulPoStart` | strict | `u1` | - |  | 106.2 | 5399 |
| R184 | real-ip | `Tests/IP/Crypto/P256SignDemoTest.lean:98` | `#synthesizeVerilog` | `synth_p256SignCore` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 19.6 | 1701 |
| R185 | real-ip | `Tests/IP/Crypto/PolicySignDemoM2Test.lean:103` | `#synthesizeVerilog` | `synth_policyM2Tx` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 27.7 | 1724 |
| R186 | real-ip | `Tests/IP/Crypto/PolicySignDemoM2Test.lean:111` | `#synthesizeVerilog` | `synth_policyM2Reject` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 27.1 | 1719 |
| R187 | real-ip | `Tests/IP/Crypto/PolicySignDemoTest.lean:120` | `#synthesizeVerilog` | `synth_policyDemoTx` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 24.6 | 1712 |
| R188 | real-ip | `Tests/IP/Crypto/PolicySignDemoTest.lean:129` | `#synthesizeVerilog` | `synth_policyDemoReject` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 25.1 | 1714 |
| R189 | real-ip | `Tests/IP/Crypto/RLPHWTest.lean:132` | `#synthesizeVerilog` | `synth_rlpHeaderByte` | strict | `u1` | - |  | 33.6 | 2939 |
| R190 | real-ip | `Tests/IP/Crypto/RLPHWTest.lean:141` | `#synthesizeVerilog` | `synth_rlpHeaderValid` | strict | `u1` | - |  | 23.6 | 2344 |
| R191 | real-ip | `Tests/IP/Crypto/RLPHWTest.lean:150` | `#synthesizeVerilog` | `synth_rlpHeaderDone` | strict | `u1` | - |  | 22.6 | 2309 |
| R192 | real-ip | `Tests/IP/Crypto/SHA256Test.lean:120` | `#synthesizeVerilog` | `synth_sha256KMux` | strict | `u1_hier+u2_hier` | - |  | 22.1 | 2015 |
| R193 | real-ip | `Tests/IP/Crypto/SHA512BlockHWTest.lean:153` | `#synthesizeVerilog` | `synth_sha512Block_out0` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:open | 15.1 | 1683 |
| R194 | real-ip | `Tests/IP/Crypto/SHA512BlockHWTest.lean:164` | `#synthesizeVerilog` | `synth_sha512Block_done` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:open | 14.6 | 1680 |
| R195 | real-ip | `Tests/IP/Crypto/SHA512HWTest.lean:149` | `#synthesizeVerilog` | `synth_sha512KMux` | strict | `u1_hier+u2_hier` | - |  | 21.6 | 2151 |
| R196 | real-ip | `Tests/IP/Crypto/Secp256k1ECDSAHWTest.lean:128` | `#synthesizeVerilog` | `synth_ecdsaR` | strict | `u1` | - |  | 137.7 | 6329 |
| R197 | real-ip | `Tests/IP/Crypto/Secp256k1ECDSAHWTest.lean:142` | `#synthesizeVerilog` | `synth_ecdsaS` | strict | `u1` | - |  | 140.2 | 6419 |
| R198 | real-ip | `Tests/IP/Crypto/Secp256k1ECDSAHWTest.lean:156` | `#synthesizeVerilog` | `synth_ecdsaDone` | strict | `u1` | - |  | 142.3 | 5771 |
| R199 | real-ip | `Tests/IP/Crypto/Secp256k1FieldHWTest.lean:89` | `#synthesizeVerilog` | `synth_secp256k1MulResult` | strict | `u1` | - |  | 30.2 | 2473 |
| R200 | real-ip | `Tests/IP/Crypto/Secp256k1FieldHWTest.lean:97` | `#synthesizeVerilog` | `synth_secp256k1MulDone` | strict | `u1` | - |  | 29.7 | 2541 |
| R201 | real-ip | `Tests/IP/Crypto/Secp256k1OrderHWTest.lean:89` | `#synthesizeVerilog` | `synth_secp256k1OrderMulResult` | strict | `u1` | - |  | 29.7 | 2481 |
| R202 | real-ip | `Tests/IP/Crypto/Secp256k1OrderHWTest.lean:97` | `#synthesizeVerilog` | `synth_secp256k1OrderMulDone` | strict | `u1` | - |  | 30.1 | 2548 |
| R203 | real-ip | `Tests/IP/Crypto/Secp256k1PointOpHWTest.lean:163` | `#synthesizeVerilog` | `synth_secp256k1PointOpX` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 241.9 | 16255 |
| R204 | real-ip | `Tests/IP/Crypto/Secp256k1PointOpHWTest.lean:174` | `#synthesizeVerilog` | `synth_secp256k1PointOpDone` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 294.9 | 12227 |
| R205 | real-ip | `Tests/IP/Crypto/Secp256k1PointOpHWTest.lean:185` | `#synthesizeVerilog` | `synth_secp256k1PointOpMulStart` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 262.9 | 9769 |
| R206 | real-ip | `Tests/IP/Crypto/Secp256k1ScalarMulHWTest.lean:135` | `#synthesizeVerilog` | `synth_secp256k1ScalarMulX` | strict | `u1` | - |  | 103.2 | 5544 |
| R207 | real-ip | `Tests/IP/Crypto/Secp256k1ScalarMulHWTest.lean:146` | `#synthesizeVerilog` | `synth_secp256k1ScalarMulDone` | strict | `u1` | - |  | 107.7 | 5897 |
| R208 | real-ip | `Tests/IP/Crypto/Secp256k1ScalarMulHWTest.lean:157` | `#synthesizeVerilog` | `synth_secp256k1ScalarMulPoStart` | strict | `u1` | - |  | 102.2 | 5438 |
| R209 | real-ip | `Tests/IP/Crypto/TxPolicyTest.lean:83` | `#synthesizeVerilog` | `synth_txPolicy` | strict | `u1` | - |  | 13.6 | 1771 |
| R210 | real-ip | `Tests/IP/Net/ARPTest.lean:201` | `#synthesizeVerilog` | `synth_arpResponderByte` | strict | `u2_hier` | U2HRStmt registers=true |  | 449.1 | 8915 |
| R211 | real-ip | `Tests/IP/Net/ARPTest.lean:213` | `#synthesizeVerilog` | `synth_arpRequesterByte` | strict | `u2_hier` | U2HRStmt registers=true |  | 611.9 | 12073 |
| R212 | real-ip | `Tests/IP/Net/CRC32Test.lean:33` | `#synthesizeVerilog` | `SynthesisChecks.crc32EngineTop` | strict | `u1` | - |  | 44.1 | 2653 |
| R213 | real-ip | `Tests/IP/Net/EthernetTest.lean:124` | `#synthesizeVerilog` | `synth_dmacOnly` | strict | `u1` | - |  | 55.7 | 4682 |
| R214 | real-ip | `Tests/IP/Net/EthernetTest.lean:138` | `#synthesizeVerilog` | `synth_rxFramerAll` | strict | `u1` | - |  | 239.3 | 4873 |
| R215 | real-ip | `Tests/IP/Net/EthernetTxTest.lean:134` | `#synthesizeVerilog` | `synth_txByteOnly` | strict | `u1` | - |  | 100.2 | 4281 |
| R216 | real-ip | `Tests/IP/Net/EthernetTxTest.lean:147` | `#synthesizeVerilog` | `synth_txFramerAll` | strict | `u1` | - |  | 168.8 | 4632 |
| R217 | real-ip | `Tests/IP/Net/HFTQuoteTest.lean:91` | `#synthesizeVerilog` | `Sparkle.IP.Net.HFTQuote.quoteBid` | strict | `u1` | - |  | 48.6 | 2325 |
| R218 | real-ip | `Tests/IP/Net/HFTQuoteTest.lean:92` | `#synthesizeVerilog` | `Sparkle.IP.Net.HFTQuote.quoteAsk` | strict | `u1` | - |  | 47.6 | 2390 |
| R219 | real-ip | `Tests/IP/Net/HFTQuoteTest.lean:93` | `#synthesizeVerilog` | `Sparkle.IP.Net.HFTQuote.quoteInv` | strict | `u1` | - |  | 44.7 | 2179 |
| R220 | real-ip | `Tests/IP/Net/HFTStrategyTest.lean:96` | `#synthesizeVerilog` | `synth_hftOutByte` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:deep | 11.6 | 1653 |
| R221 | real-ip | `Tests/IP/Net/HFTStrategyTest.lean:104` | `#synthesizeVerilog` | `synth_hftEmitCount` | strict | `u1` | - |  | 21.6 | 2227 |
| R222 | real-ip | `Tests/IP/Net/HFTStrategyTest.lean:112` | `#synthesizeVerilog` | `synth_hftTriggerSeen` | strict | `u1` | - |  | 19.1 | 2410 |
| R223 | real-ip | `Tests/IP/Net/HTTPTest.lean:138` | `#synthesizeVerilog` | `synth_httpGetByte` | strict | `u2_hier` | U2HRStmt registers=true |  | 26.2 | 2088 |
| R224 | real-ip | `Tests/IP/Net/HTTPTest.lean:145` | `#synthesizeVerilog` | `synth_httpRespByte` | strict | `u2_hier` | U2HRStmt registers=true |  | 32.2 | 2569 |
| R225 | real-ip | `Tests/IP/Net/HTTPTest.lean:153` | `#synthesizeVerilog` | `synth_httpRequestParser` | strict | `u1` | - |  | 19.1 | 2103 |
| R226 | real-ip | `Tests/IP/Net/HTTPTest.lean:161` | `#synthesizeVerilog` | `synth_httpStatus` | strict | `u1` | - |  | 23.2 | 2423 |
| R227 | real-ip | `Tests/IP/Net/ICMPTest.lean:148` | `#synthesizeVerilog` | `synth_icmpResponderByte` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:signal | 11.1 | 1658 |
| R228 | real-ip | `Tests/IP/Net/ICMPTest.lean:158` | `#synthesizeVerilog` | `synth_icmpRequesterByte` | strict | `u2_hier` | U2HRStmt registers=true |  | 248.0 | 7158 |
| R229 | real-ip | `Tests/IP/Net/ICMPTest.lean:168` | `#synthesizeVerilog` | `synth_icmpRequesterReplyOk` | strict | `u1` | - |  | 82.7 | 3682 |
| R230 | real-ip | `Tests/IP/Net/IPv4Test.lean:153` | `#synthesizeVerilog` | `synth_ipv4TxByte` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:conns | 11.1 | 1659 |
| R231 | real-ip | `Tests/IP/Net/IPv4Test.lean:161` | `#synthesizeVerilog` | `synth_ipv4RxSrcIp` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:external-timeout | 11.1 | 1656 |
| R232 | real-ip | `Tests/IP/Net/IPv4Test.lean:169` | `#synthesizeVerilog` | `synth_ipv4RxHeaderOk` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:external-timeout | 11.1 | 1659 |
| R233 | real-ip | `Tests/IP/Net/SLIPTest.lean:191` | `#synthesizeVerilog` | `synth_slipFramerByte` | strict | `u1` | - |  | 26.7 | 2510 |
| R234 | real-ip | `Tests/IP/Net/SLIPTest.lean:192` | `#synthesizeVerilog` | `synth_slipDeframerByte` | strict | `u1` | - |  | 26.1 | 2486 |
| R235 | real-ip | `Tests/IP/Net/TCPHeaderTest.lean:117` | `#synthesizeVerilog` | `synth_tcpHeaderByte` | strict | `u1_hier+u2_hier` | - |  | 40.7 | 2838 |
| R236 | real-ip | `Tests/IP/Net/TCPHeaderTest.lean:131` | `#synthesizeVerilog` | `synth_tcpChecksum` | strict | `u2_hier` | U2HStmt registers=false |  | 41.2 | 4364 |
| R237 | real-ip | `Tests/IP/Net/TCPHeaderTest.lean:140` | `#synthesizeVerilog` | `synth_tcpRxSeq` | strict | `u1` | - |  | 84.2 | 5918 |
| R238 | real-ip | `Tests/IP/Net/TCPHeaderTest.lean:148` | `#synthesizeVerilog` | `synth_tcpRxFlags` | strict | `u1` | - |  | 86.7 | 6016 |
| R239 | real-ip | `Tests/IP/Net/TCPStateTest.lean:201` | `#synthesizeVerilog` | `synth_serverFsmState` | strict | `u1` | - |  | 40.1 | 3124 |
| R240 | real-ip | `Tests/IP/Net/TCPStateTest.lean:210` | `#synthesizeVerilog` | `synth_serverFsmEstablished` | strict | `u1` | - |  | 40.1 | 3124 |
| R241 | real-ip | `Tests/IP/Net/TCPStateTest.lean:219` | `#synthesizeVerilog` | `synth_serverFsmTxReq` | strict | `u1` | - |  | 41.2 | 3189 |
| R242 | real-ip | `Tests/IP/Net/TCPStateTest.lean:229` | `#synthesizeVerilog` | `synth_clientFsmState` | strict | `u1` | - |  | 60.2 | 4113 |
| R243 | real-ip | `Tests/IP/Net/TCPStateTest.lean:239` | `#synthesizeVerilog` | `synth_clientFsmEstablished` | strict | `u1` | - |  | 60.8 | 4173 |
| R244 | real-ip | `Tests/IP/Net/UARTTest.lean:135` | `#synthesizeVerilog` | `synth_uartTx` | strict | `u1` | - |  | 23.7 | 2584 |
| R245 | real-ip | `Tests/IP/Net/UARTTest.lean:136` | `#synthesizeVerilog` | `synth_uartRx` | strict | `u1` | - |  | 25.7 | 2326 |
| R246 | real-ip | `Tests/IP/Net/UsbWebServerSynth.lean:22` | `#synthesizeVerilog` | `Sparkle.Tests.IP.Net.UsbWebServerSynth.synth_usbWebServer` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:open | 11.1 | 1668 |
| R247 | real-ip | `Tests/IP/USB/Fido2DemoTest.lean:102` | `#synthesizeVerilog` | `synth_fido2Tx` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 21.6 | 1706 |
| R248 | real-ip | `Tests/IP/USB/Fido2DemoTest.lean:106` | `#synthesizeVerilog` | `synth_fido2Done` | refused | `u1` | - | u1:order; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 26.6 | 1733 |
| R249 | regression | `Tests/RunCircuitHTest.lean:104` | `#synthesizeVerilog` | `Sparkle.Tests.RunCircuitHTest.counterH` | strict | `u1` | - |  | 14.9 | 1683 |
| R250 | regression | `Tests/RunCircuitHTest.lean:105` | `#synthesizeVerilog` | `Sparkle.Tests.RunCircuitHTest.twoCountH` | strict | `u1` | - |  | 18.2 | 1747 |
| R251 | regression | `Tests/RunCircuitHTest.lean:106` | `#synthesizeVerilog` | `Sparkle.Tests.RunCircuitHTest.mixedWidthH` | strict | `u1` | - |  | 16.3 | 1795 |
| R252 | regression | `Tests/RunCircuitHTest.lean:107` | `#synthesizeVerilog` | `Sparkle.Tests.RunCircuitHTest.tripleCountH` | strict | `u1` | - |  | 18.3 | 1960 |
| R253 | regression | `Tests/RunCircuitHTest.lean:108` | `#synthesizeVerilog` | `Sparkle.Tests.RunCircuitHTest.fourCountH` | strict | `u1` | - |  | 20.8 | 2085 |
| R254 | regression | `Tests/RunCircuitHTest.lean:109` | `#synthesizeVerilog` | `Sparkle.Tests.RunCircuitHTest.threeCountForM` | strict | `u1` | - |  | 16.6 | 1915 |
| R255 | regression | `Tests/SignalLoopTest.lean:115` | `#synthesizeVerilog` | `Sparkle.Tests.SignalLoopTest.counterLoop` | strict | `u1` | - |  | 15.0 | 1712 |
| R256 | regression | `Tests/SignalLoopTest.lean:116` | `#synthesizeVerilog` | `Sparkle.Tests.SignalLoopTest.counterDSL` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 13.2 | 1725 |
| R257 | regression | `Tests/SignalLoopTest.lean:117` | `#synthesizeVerilog` | `Sparkle.Tests.SignalLoopTest.counterEnableLoop` | strict | `u1` | - |  | 15.2 | 1688 |
| R258 | regression | `Tests/SignalLoopTest.lean:118` | `#synthesizeVerilog` | `Sparkle.Tests.SignalLoopTest.counterEnableDSL` | strict | `u1+u1_deep+u1_deep_ns` | - |  | 14.1 | 1704 |
| R259 | regression | `Tests/SignalLoopTest.lean:119` | `#synthesizeVerilog` | `Sparkle.Tests.SignalLoopTest.shift4Loop` | strict | `u1` | - |  | 13.3 | 1679 |
| R260 | regression | `Tests/SymbolicParameterEmit.lean:4` | `#synthesizeParameterizedVerilog` |  | unmeasured |  | - | u1:unsupported-invocation; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:unsupported-invocation; u1_mem_packed:unsupported-invocation; u1_packed:unsupported-invocation; u2_hier:unsupported-invocation |  |  |
| R261 | regression | `Tests/SymbolicParameterEmit.lean:5` | `#synthesizeParameterizedVerilog` |  | unmeasured |  | - | u1:unsupported-invocation; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:unsupported-invocation; u1_mem_packed:unsupported-invocation; u1_packed:unsupported-invocation; u2_hier:unsupported-invocation |  |  |
| R262 | regression | `Tests/SymbolicParameterEmit.lean:6` | `#synthesizeParameterizedVerilog` |  | unmeasured |  | - | u1:unsupported-invocation; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:unsupported-invocation; u1_mem_packed:unsupported-invocation; u1_packed:unsupported-invocation; u2_hier:unsupported-invocation |  |  |
| R263 | regression | `Tests/SymbolicParameterEmit.lean:7` | `#synthesizeParameterizedVerilog` |  | unmeasured |  | - | u1:unsupported-invocation; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:unsupported-invocation; u1_mem_packed:unsupported-invocation; u1_packed:unsupported-invocation; u2_hier:unsupported-invocation |  |  |
| R264 | regression | `Tests/Synthesis/SynthCatalog.lean:22` | `#synthesizeVerilog` | `synth_pure` | strict | `u1` | - |  | 15.2 | 1703 |
| R265 | regression | `Tests/Synthesis/SynthCatalog.lean:30` | `#synthesizeVerilog` | `synth_add` | strict | `u1` | - |  | 14.0 | 1710 |
| R266 | regression | `Tests/Synthesis/SynthCatalog.lean:35` | `#synthesizeVerilog` | `synth_sub` | strict | `u1` | - |  | 13.1 | 1703 |
| R267 | regression | `Tests/Synthesis/SynthCatalog.lean:40` | `#synthesizeVerilog` | `synth_mul` | strict | `u1` | - |  | 13.1 | 1706 |
| R268 | regression | `Tests/Synthesis/SynthCatalog.lean:48` | `#synthesizeVerilog` | `synth_and` | strict | `u1` | - |  | 13.8 | 1709 |
| R269 | regression | `Tests/Synthesis/SynthCatalog.lean:53` | `#synthesizeVerilog` | `synth_or` | strict | `u1` | - |  | 13.8 | 1708 |
| R270 | regression | `Tests/Synthesis/SynthCatalog.lean:58` | `#synthesizeVerilog` | `synth_xor` | strict | `u1` | - |  | 13.8 | 1703 |
| R271 | regression | `Tests/Synthesis/SynthCatalog.lean:66` | `#synthesizeVerilog` | `synth_shl` | strict | `u1` | - |  | 14.4 | 1709 |
| R272 | regression | `Tests/Synthesis/SynthCatalog.lean:71` | `#synthesizeVerilog` | `synth_shr` | strict | `u1` | - |  | 13.7 | 1713 |
| R273 | regression | `Tests/Synthesis/SynthCatalog.lean:80` | `#synthesizeVerilog` | `synth_mux` | strict | `u1` | - |  | 12.7 | 1675 |
| R274 | regression | `Tests/Synthesis/SynthCatalog.lean:88` | `#synthesizeVerilog` | `synth_reg` | strict | `u1` | - |  | 12.6 | 1704 |
| R275 | regression | `Tests/Synthesis/SynthCatalog.lean:96` | `#synthesizeVerilog` | `synth_eq` | strict | `u1` | - |  | 24.1 | 3678 |
| R276 | regression | `Tests/Synthesis/SynthCatalog.lean:104` | `#synthesizeVerilog` | `synth_slice` | strict | `u1` | - |  | 13.2 | 1709 |
| R277 | regression | `Tests/Synthesis/SynthCatalog.lean:112` | `#synthesizeVerilog` | `synth_neg` | strict | `u1` | - |  | 14.3 | 1705 |
| R278 | regression | `Tests/Synthesis/SynthCatalog.lean:121` | `#synthesizeVerilog` | `synth_concat` | strict | `u1` | - |  | 15.3 | 1714 |
| R279 | regression | `Tests/Synthesis/SynthCatalog.lean:131` | `#synthesizeVerilog` | `synth_let` | strict | `u1` | - |  | 13.3 | 1710 |
| R280 | regression | `Tests/Synthesis/SynthCatalog.lean:139` | `#synthesizeVerilog` | `synth_sext` | strict | `u1` | - |  | 13.8 | 1708 |
| R281 | regression | `Tests/Synthesis/SynthCatalog.lean:151` | `#synthesizeVerilog` | `synth_scale` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:proof; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 223.8 | 3439 |
| R282 | regression | `Tests/Synthesis/SynthCatalog.lean:171` | `#synthesizeVerilog` | `synth_tree` | strict | `u1` | - |  | 16.4 | 1683 |
| R283 | regression | `Tests/Synthesis/SynthCatalog.lean:181` | `#synthesizeVerilog` | `synth_mux_eq` | strict | `u1` | - |  | 15.7 | 1717 |
| R284 | regression | `Tests/Synthesis/SynthCatalog.lean:194` | `#synthesizeVerilog` | `synth_bus_split` | strict | `u1` | - |  | 14.2 | 1708 |
| R285 | regression | `Tests/Synthesis/SynthCatalog.lean:203` | `#synthesizeVerilog` | `synth_bus_pack` | strict | `u1` | - |  | 13.6 | 1723 |
| R286 | regression | `Tests/Synthesis/SynthCatalog.lean:215` | `#synthesizeVerilog` | `synth_bundle` | strict | `u1` | - |  | 14.2 | 1659 |
| R287 | regression | `Tests/Synthesis/SynthCatalog.lean:227` | `#synthesizeVerilog` | `synth_field_write` | strict | `u1` | - |  | 17.3 | 1655 |
| R288 | regression | `Tests/Synthesis/SynthCatalog.lean:240` | `#synthesizeVerilog` | `synth_mmio_mux` | strict | `u1` | - |  | 17.1 | 1734 |
| R289 | regression | `Tests/Synthesis/SynthCatalog.lean:250` | `#synthesizeVerilog` | `synth_loop_counter` | strict | `u1` | - |  | 14.3 | 1699 |
| R290 | regression | `Tests/Synthesis/SynthCatalog.lean:271` | `#synthesizeVerilog` | `synth_loop_fsm` | strict | `u1_packed` | - |  | 14.6 | 1842 |
| R291 | regression | `Tests/Synthesis/SynthCatalog.lean:292` | `#synthesizeVerilog` | `synth_loop_bram` | refused | `u1` | - | u1:proof; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:hier-shape | 12.2 | 1676 |
| R292 | regression | `Tests/Synthesis/SynthCatalog.lean:300` | `#synthesizeVerilog` | `synth_ashr` | strict | `u1` | - |  | 12.6 | 1720 |
| R293 | regression | `Tests/SynthesisTests.lean:64` | `#synthesizeVerilog` | `test_add` | strict | `u1` | - |  | 12.1 | 1709 |
| R294 | regression | `Tests/SynthesisTests.lean:65` | `#synthesizeVerilog` | `test_sub` | strict | `u1` | - |  | 12.2 | 1693 |
| R295 | regression | `Tests/SynthesisTests.lean:68` | `#synthesizeVerilogDesign` | `test_hierarchical_alu` | strict | `u1` | - |  | 13.3 | 1709 |
| R296 | regression | `Tests/SynthesisTests.lean:71` | `#synthesizeVerilog` | `test_tuple` | strict | `u1_packed` | - |  | 12.6 | 1661 |
| R297 | regression | `Tests/SynthesisTests.lean:72` | `#synthesizeVerilog` | `test_tuple_extract` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 12.7 | 1602 |
| R298 | regression | `Tests/SynthesisTests.lean:78` | `#synthesizeVerilog` | `test_mux2` | strict | `u1` | - |  | 13.2 | 1641 |
| R299 | regression | `Tests/SynthesisTests.lean:93` | `#synthesizeVerilog` | `test_simple_register` | strict | `u1` | - |  | 13.2 | 1682 |
| R300 | regression | `Tests/TestCompilerExtensions.lean:26` | `#synthesizeVerilog` | `test_shl` | strict | `u1` | - |  | 13.7 | 1646 |
| R301 | regression | `Tests/TestCompilerExtensions.lean:35` | `#synthesizeVerilog` | `test_shr` | strict | `u1` | - |  | 13.1 | 1642 |
| R302 | regression | `Tests/TestCompilerExtensions.lean:44` | `#synthesizeVerilog` | `test_neg` | strict | `u1` | - |  | 14.3 | 1640 |
| R303 | regression | `Tests/TestCompilerExtensions.lean:53` | `#synthesizeVerilog` | `test_not` | strict | `u1` | - |  | 14.7 | 1639 |
| R304 | regression | `Tests/TestCompilerExtensions.lean:63` | `#synthesizeVerilog` | `test_slice_map` | strict | `u1` | - |  | 14.7 | 1640 |
| R305 | regression | `Tests/TestCompilerExtensions.lean:72` | `#synthesizeVerilog` | `test_slice_upper` | strict | `u1` | - |  | 14.2 | 1640 |
| R306 | regression | `Tests/TestCompilerExtensions.lean:82` | `#synthesizeVerilog` | `test_concat` | strict | `u1` | - |  | 14.7 | 1641 |
| R307 | regression | `Tests/TestCompilerExtensions.lean:92` | `#synthesizeVerilog` | `test_reg_enable` | strict | `u1` | - |  | 14.1 | 1648 |
| R308 | regression | `Tests/TestCompilerExtensions.lean:102` | `#synthesizeVerilog` | `test_extract_opcode` | strict | `u1` | - |  | 14.2 | 1644 |
| R309 | regression | `Tests/TestCompilerExtensions.lean:114` | `#synthesizeVerilog` | `test_decoder_fields` | strict | `u1_packed` | - |  | 13.6 | 1644 |
| R310 | regression | `Tests/TestConditionals.lean:52` | `#synthesizeVerilog` | `test_mux_RIGHT` | strict | `u1` | - |  | 14.8 | 1640 |
| R311 | regression | `Tests/TestConditionals.lean:53` | `#synthesizeVerilog` | `add_or_sub` | strict | `u1` | - |  | 15.2 | 1662 |
| R312 | regression | `Tests/TestDRC.lean:17` | `#synthesizeVerilog` | `drc_combo_output` | strict | `u1` | - |  | 14.7 | 1637 |
| R313 | regression | `Tests/TestDRC.lean:23` | `#synthesizeVerilog` | `drc_registered_output` | strict | `u1` | - |  | 14.7 | 1656 |
| R314 | regression | `Tests/TestErrorDetection.lean:68` | `#synthesizeVerilog` | `test_mux_works` | refused | `u1` | - | u1:case-error; u1_deep:prep; u1_deep_ns:prep; u1_hier:proof; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 12.1 | 1706 |
| R315 | regression | `Tests/TestErrorDetection.lean:69` | `#synthesizeVerilog` | `test_fst_snd_works` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 13.1 | 1626 |
| R316 | regression | `Tests/TestErrorDetection.lean:70` | `#synthesizeVerilog` | `test_proj3_works` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 12.1 | 1602 |
| R317 | regression | `Tests/TestUnbundle2.lean:66` | `#synthesizeVerilog` | `test_projection_RIGHT` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 12.7 | 1604 |
| R318 | regression | `Tests/TestUnbundle2.lean:67` | `#synthesizeVerilog` | `useHalfAdder` | strict | `u1` | - |  | 23.1 | 2971 |
| R319 | regression | `Tests/TupleProjectionTest.lean:72` | `#synthesizeVerilog` | `example_2tuple_fst` | refused | `u1` | - | u1:table; u1_deep:prep; u1_deep_ns:prep; u1_hier:table; u1_mem_packed:table; u1_packed:table; u2_hier:table | 14.1 | 1605 |
| R320 | regression | `Tests/TupleProjectionTest.lean:73` | `#synthesizeVerilog` | `addThreeNumbers` | strict | `u1` | - |  | 15.6 | 1668 |
| R321 | regression | `Tests/Tutorial/HierarchyTest.lean:68` | `#writeVerilogDesign` |  | unmeasured |  | - | u1:unsupported-invocation; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:unsupported-invocation; u1_mem_packed:unsupported-invocation; u1_packed:unsupported-invocation; u2_hier:unsupported-invocation |  |  |
| R322 | regression | `Tests/Tutorial/HierarchyTest.lean:69` | `#writeVerilogDesign` |  | unmeasured |  | - | u1:unsupported-invocation; u1_deep:unsupported-invocation; u1_deep_ns:unsupported-invocation; u1_hier:unsupported-invocation; u1_mem_packed:unsupported-invocation; u1_packed:unsupported-invocation; u2_hier:unsupported-invocation |  |  |
| R323 | regression | `Tests/VerifyVerilog.lean:52` | `#synthesizeVerilog` | `test_add` | refused | `u1` | - | u1:case-error; u1_deep:prep; u1_deep_ns:prep; u1_hier:proof; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 15.2 | 1640 |
| R324 | regression | `Tests/VerifyVerilog.lean:68` | `#synthesizeVerilog` | `test_and` | refused | `u1` | - | u1:case-error; u1_deep:prep; u1_deep_ns:prep; u1_hier:proof; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 13.6 | 1636 |
| R325 | regression | `Tests/VerifyVerilog.lean:82` | `#synthesizeVerilog` | `test_mux` | refused | `u1` | - | u1:case-error; u1_deep:prep; u1_deep_ns:prep; u1_hier:proof; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 13.6 | 1646 |
| R326 | regression | `Tests/VerifyVerilog.lean:95` | `#synthesizeVerilogDesign` | `test_hierarchical_alu` | refused | `u1` | - | u1:case-error; u1_deep:prep; u1_deep_ns:prep; u1_hier:proof; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 14.1 | 1652 |
| R327 | regression | `Tests/VerifyVerilog.lean:112` | `#synthesizeVerilog` | `test_flipflop` | refused | `u1` | - | u1:case-error; u1_deep:prep; u1_deep_ns:prep; u1_hier:hier-shape; u1_mem_packed:packed; u1_packed:packed; u2_hier:scope | 13.6 | 1641 |
