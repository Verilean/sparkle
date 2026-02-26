# Sparkle SoC — Current Status

**Date**: 2026-02-27
**Branch**: main (`55b38be`)

---

## SoC Synthesis (Phase 9)

`#synthesizeVerilog rv32iSoCSynth` generates 9 SystemVerilog modules with 119 registers.

### Generated Modules

1. `Sparkle_Examples_RV32_aluSignal`
2. `Sparkle_Examples_RV32_branchCompSignal`
3. `Sparkle_Examples_RV32_hazardSignal`
4. `Sparkle_Examples_RV32_decoderFieldsSignal`
5. `Sparkle_Examples_RV32_immGenSignal`
6. `Sparkle_Examples_RV32_aluControlSignal`
7. `Sparkle_Examples_RV32_controlSignalsSignal`
8. `Sparkle_Examples_RV32_Divider_dividerSignal` (multi-cycle restoring divider)
9. `Sparkle_Examples_RV32_SoCVerilog_rv32iSoCSynth` (top module, 119 registers)

### Register Map (119 registers)

| Range | Count | Description |
|-------|-------|-------------|
| 0-5 | 6 | IF stage: pcReg, fetchPC, flushDelay, ifid_inst/pc/pc4 |
| 6-29 | 24 | ID/EX pipeline registers |
| 30-31 | 2 | EX/WB: exwb_alu, exwb_physAddr |
| 32-38 | 7 | EX/WB: rd, regW, m2r, pc4, jump, isCsr, csrRdata |
| 39-44 | 6 | WB forwarding + store history |
| 45-49 | 5 | CLINT: msip, mtime, mtimecmp |
| 50-56 | 7 | CSR M-mode |
| 57-58 | 2 | AI MMIO |
| 59-60 | 2 | Sub-word + M-ext |
| 61-69 | 9 | A-ext (reservation, AMO, pending write) |
| 70-79 | 10 | S-mode CSRs + privilege + delegation |
| 80-107 | 28 | MMU: 4-entry TLB + PTW FSM |
| 108-109 | 2 | SRET + SFENCE.VMA |
| 110-115 | 6 | UART 8250 |
| 116-117 | 2 | mcounteren, scounteren |
| 118 | 1 | divPending |

### Key Architecture Decisions

1. **`unfoldDefinition?` instead of `whnf`**: Prevents exponential blowup on 119-register tuple projections
2. **Multi-cycle restoring divider** (~34 cycles): `Signal.loop` sub-module with `divPending`, `divStall`, `divAbort`
3. **Duplicated memory arrays**: `Signal.memory` + `Signal.memoryComboRead` stay in sync via identical writes
4. **Non-synthesizable functions replaced**: `mextCompute` → `mulComputeSignal` + `dividerSignal`; `amoCompute` → `amoComputeSignal`

---

## Remaining Work

### Verilator Testing (Phase 9 cont.)

| # | Task | Status |
|---|------|--------|
| 1 | `lake build Examples.RV32.SoCVerilog` — synthesis succeeds | Done |
| 2 | Create `verilator/rv32i_soc_wrapper.sv` — unpack packed output | TODO |
| 3 | Update `verilator/Makefile` for generated SV + wrapper | TODO |
| 4 | Verilator build with generated SV | TODO |
| 5 | Compare generated SV structure with hand-written `rv32i_soc.sv` | TODO |
| 6 | Firmware tests pass (simple program) | TODO |
| 7 | Linux boot test (OpenSBI → kernel → UART output) | TODO |

**Known differences from hand-written SV**:
- Multi-cycle divider (34 cycles) vs combinational `/` `%` (1 cycle) — Linux boot will be slower
- Duplicated DMEM (64MB vs 32MB memory in simulation)
- Packed output vs named ports — wrapper needed

### Linux Boot Debugging

- SLUB allocator crash at `epc: 0xc006fa84` in `__slab_alloc_node` (NULL pointer dereference)
- Could be remaining data corruption or kernel config issue
- Try `CONFIG_SLUB_TINY` or `CONFIG_SLAB`, or older kernel (5.x)

### SoC Improvements

- [ ] Debug infrastructure cleanup (remove unused debug ports/traces)
- [ ] Investigate PTW + DMEM port sharing edge cases
- [ ] Interrupt controller (PLIC)
- [ ] Timer interrupt handling (CLINT timer compare)
- [ ] Instruction cache, branch predictor
- [ ] FPGA synthesis targeting

---

## Build & Test Commands

```bash
# Lean build (SoC simulation)
lake build Examples.RV32.SoC

# Lean build (Verilog synthesis)
lake build Examples.RV32.SoCVerilog

# Verilator build (hand-written SV)
cd verilator && make build

# Firmware test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000

# Linux boot test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
```
