# Sparkle Project — TODO

## Current Status (2026-02-27)

### Completed Phases
- [x] Phase 1: Sub-word memory access (LB/LH/LBU/LHU/SB/SH)
- [x] Phase 2: M extension (MUL/DIV/REM)
- [x] Phase 3: A extension (atomics LR.W/SC.W/AMO)
- [x] Phase 4: Sparse memory (32 MB DMEM)
- [x] Phase 5: S-mode, Sv32 MMU (TLB + PTW), trap delegation
- [x] Phase 6: UART RX (8250-compatible register interface)
- [x] Phase 7: OpenSBI + Device Tree
- [x] Phase 8: Linux kernel boot (OpenSBI v0.9 + Linux 6.6.0)

### Phase 8 Result
Linux 6.6.0 boots on Sparkle RV32IMA SoC in Verilator, printing:
```
Linux version 6.6.0 ... #6 Thu Feb 26 06:29:23 UTC 2026
Machine model: Sparkle RV32IMA SoC
Memory: 26208K/28672K available
```
Kernel panic in `kmem_cache_init` (SLUB allocator NULL pointer dereference).

---

## High Priority

### Debug SLUB allocator crash
- Crash at `epc: 0xc006fa84` in `__slab_alloc_node`
- Call chain: `start_kernel -> mm_core_init -> kmem_cache_init -> create_boot_cache -> __kmem_cache_create -> kmem_cache_alloc_node -> slab_alloc_node -> __slab_alloc_node`
- `badaddr: 0x00000004`, `cause: 0x0000000d` (load page fault)
- Register `a0 = 0x00000000` (NULL slab page pointer)
- Could be remaining data corruption from pipeline bugs, or kernel config issue
- Investigate: add per-cycle trace around cycle ~5.5M, check if store-forwarding or PTW interaction corrupts slab data

### Port Verilator bug fixes back to SoC.lean
- `exwb_physAddr` pipeline register (Bug #1: WB bus decode must use physical address)
- `holdEX` mechanism (Bug #2: freeze EX when pendingWriteEn hijacks DMEM port)
- `fetchPC_next` flush fix (Bug #3: use `pcReg_next` on flush, not stale `pcReg`)
- These fixes are in `verilator/rv32i_soc.sv` but NOT yet in `Examples/RV32/SoC.lean`

---

## Medium Priority

### Clean up debug infrastructure
- Remove unused iTLB debug output ports from `rv32i_soc.sv` module interface
- Remove commented-out debug traces (PTW, PGFAULT, D-TLB-MISS, BOOT, VERIFY)
- Remove duplicate TRAP logging that was in `tb_soc.cpp`
- Consider adding a `DEBUG` parameter to gate `$display` statements

### Investigate PTW + DMEM port sharing
- `ptwMemActive` can hijack `dmem_addr` similarly to `pendingWriteEn`
- Current analysis suggests timing is safe (PTW state is registered)
- But edge cases may exist with simultaneous I-TLB miss + D-side load
- May need `holdEX`-like treatment for `ptwMemActive` if further corruption found

### Kernel configuration tuning
- Try `CONFIG_SLUB_TINY` or `CONFIG_SLAB` instead of default SLUB
- Try older kernel (5.x) with simpler allocator requirements
- Increase DRAM beyond 32MB if needed (address space allows 512MB)

---

## Low Priority / Future

### SoC features
- [ ] Interrupt controller (PLIC) for external interrupts
- [ ] Timer interrupt handling (CLINT timer compare)
- [ ] DMA controller
- [ ] SPI/I2C peripheral for external device access
- [ ] Instruction cache (reduce IMEM access latency)
- [ ] Branch predictor

### Synthesis
- [ ] Auto-generate SystemVerilog from Lean Signal DSL (`#synthesizeVerilog`)
  - Requires `memoryComboRead` support in compiler
  - Current SoC uses hand-written `rv32i_soc.sv`
- [ ] FPGA synthesis targeting (Xilinx/Intel)

### YOLOv8 Accelerator
- [ ] Fix synthesis errors in C2f/SPPF/Neck ("Unbound variable")
- [ ] Fix ConvBnSiLU synthesis ("if-then-else" not supported)
- [ ] Integration test with full backbone pipeline
- [ ] Weight loading from external memory

---

## Build & Test Commands

```bash
# Lean build
lake build Examples.RV32.SoC

# Verilator build
cd verilator && make build

# Firmware tests (all must pass)
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000

# OpenSBI boot test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 5000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb

# Linux kernel boot test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
```
