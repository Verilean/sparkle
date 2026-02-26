# Phase 8: OpenSBI Boot + Linux Kernel Boot — Status

## Result: Linux Kernel Boot SUCCESS

**Linux 6.6.0 boots on the Sparkle RV32IMA SoC in Verilator.**

Key output:
```
Linux version 6.6.0 (root@c3aa9f901d5a) (riscv64-linux-gnu-gcc ...) #6 Thu Feb 26 06:29:23 UTC 2026
Machine model: Sparkle RV32IMA SoC
Memory: 26208K/28672K available (1279K kernel code, 465K rwdata, 136K rodata, 112K init, 171K bss, 2464K reserved)
```

Boot reaches `kmem_cache_init` (SLUB allocator) before hitting a NULL pointer dereference — deep into early kernel init. 3944 UART bytes output in ~7M cycles.

---

## Completed Steps

### Step 1: Add mcounteren + scounteren CSRs (SoC.lean)
- Added registers 115-116 (total 115 -> 117)
- CSR addresses: mcounteren (0x306), scounteren (0x106)

### Step 2: Add mcounteren + scounteren CSRs (rv32i_soc.sv)
- Register declarations, CSR read mux, write logic, reset, sequential update

### Step 3: Add --payload flag to tb_soc.cpp
- `--payload <file>` loads binary at 0x80400000 (4MB-aligned for Sv32 megapages)

### Step 4: Update device tree bootargs
- `bootargs = "earlycon=sbi console=ttyS0"`

### Step 5: Build & boot OpenSBI v0.9
- Full banner printed, platform detected as Sparkle RV32IMA SoC
- ISA: rv32imasu, MIDELEG: 0x00000222, MEDELEG: 0x0000b109

### Step 5b: Fix MRET decoder bug
- `csrw medeleg` misidentified as MRET; added `funct3 == 0` check

### Step 5c: Add PMP CSR stubs
- PMP CSR addresses (0x3A0-0x3EF) return 0 on read, writes ignored

### Step 6: Build Linux kernel 6.6.0
- `rv32_defconfig` with SMP disabled, SERIAL_8250 enabled, earlycon=sbi
- Kernel Image at `/tmp/linux/arch/riscv/boot/Image` (~2MB)

### Step 7: Linux boot debugging — 3 critical bug fixes

#### Bug #1: WB bus decode used virtual address (FIXED)
- **Root Cause**: WB-stage bus decode (`isCLINT_wb`, `is_mmio_wb`, `isDMEM_wb`) used `exwb_alu` (virtual address) instead of physical address
- **Symptom**: `lw ra, 12(sp)` at kernel virtual address 0xC0xxxxxx returned 0 because `is_mmio_wb = exwb_alu[30] = 1` (bit 30 of virtual address), routing the load to MMIO (returns 0) instead of DMEM
- **Fix**: Added `exwb_physAddr` pipeline register carrying `effectiveAddr` (physical address from EX stage). All WB-stage bus decode now uses `exwb_physAddr`.

#### Bug #2: pendingWriteEn hijacks DMEM address during load (FIXED)
- **Root Cause**: `dmem_addr = pendingWriteEn ? pendingWriteAddr[24:2] : dmem_addr_ex` — when `pendingWriteEn=1` (AMO writeback), DMEM reads from wrong address. Pipeline stall squashed ID/EX but still advanced EX→WB with wrong DMEM data.
- **Symptom**: Load after AMO got data from AMO's write address instead of load's address
- **Fix**: Added `holdEX` mechanism — freezes ID/EX registers and suppresses EX/WB side-effects during `pendingWriteEn`. Load re-executes in EX with correct DMEM address when holdEX clears.

#### Bug #3: Stale fetchPC after flush causes spurious page fault (FIXED)
- **Root Cause**: `fetchPC_next = stall ? fetchPC : pcReg` — on flush (MRET/branch/trap), fetchPC got the OLD pcReg instead of the flush target. In S-mode, the stale M-mode address (0x8000xxxx) triggered iTLB translation, which failed (no mapping), causing a spurious instruction page fault.
- **Symptom**: After SBI ecall return (MRET), kernel received spurious instruction page fault at OpenSBI's physical address, causing trap handler crash
- **Fix**: `fetchPC_next = flush ? pcReg_next : (stall ? fetchPC : pcReg)` — fetchPC immediately points to flush target.

---

## Kernel Boot Log (key lines)

```
OpenSBI v0.9 — Platform: Sparkle RV32IMA SoC — ISA: rv32imasu
Linux version 6.6.0 ... #6 Thu Feb 26 06:29:23 UTC 2026
Machine model: Sparkle RV32IMA SoC
SBI specification v0.2 detected
earlycon: sbi0 at I/O port 0x0 — bootconsole [sbi0] enabled
Zone ranges: Normal [mem 0x80400000-0x81ffffff]
riscv: base ISA extensions
Memory: 26208K/28672K available
Oops [#1] — NULL pointer dereference at 0x00000004
  epc: c006fa84 (__slab_alloc_node) cause: 0000000d (load page fault)
  Call: __slab_alloc_node <- kmem_cache_alloc_node <- __kmem_cache_create
        <- create_boot_cache <- kmem_cache_init <- mm_core_init <- start_kernel
Kernel panic: Attempted to kill the idle task!
```

---

## Key Files Modified (Phase 8)

| File | Status | Description |
|------|--------|-------------|
| `verilator/rv32i_soc.sv` | Done | exwb_physAddr, holdEX, fetchPC flush fix, CSRs, PMP stubs, debug cleanup |
| `verilator/tb_soc.cpp` | Done | `--payload` flag, debug cleanup |
| `Examples/RV32/SoC.lean` | Done | +2 CSR registers, MRET decoder fix |
| `firmware/sparkle-soc.dts` | Done | bootargs for earlycon |

## Remaining Work (Future)

- [ ] Debug SLUB allocator crash (NULL pointer in `__slab_alloc_node`)
- [ ] Port rv32i_soc.sv bug fixes (exwb_physAddr, holdEX, fetchPC) back to SoC.lean
- [ ] Clean up debug output ports (iTLB signals, etc.)
