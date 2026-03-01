# Sparkle SoC — Current Status

**Date**: 2026-03-01
**Branch**: main

---

## C++ Simulation Backend (Phase 10) — DONE

JIT simulator foundation: generates C++ code from IR (`Module`/`Design`), producing a C++ class with `eval()`/`tick()`/`reset()` methods. Phase 1 is purely string generation (no compilation or FFI loading).

### Completed

| # | Task | Status |
|---|------|--------|
| 1 | `Sparkle/Backend/CppSim.lean` — C++ code generator (~280 lines) | Done |
| 2 | `Tests/TestCppSim.lean` — 25 tests (counter, memory, combinational, registered memory) | Done |
| 3 | Integrated into `Sparkle.lean` and `Tests/AllTests.lean` | Done |
| 4 | `lake build` + `lake test` — all 25 CppSim tests pass | Done |

### Architecture

- Mirrors `Sparkle/Backend/Verilog.lean`: same IR traversal, different target language
- **Type mapping**: `bit`/`bv≤8` → `uint8_t`, `bv≤16` → `uint16_t`, `bv≤32` → `uint32_t`, else `uint64_t`, arrays → `std::array<T,N>`
- **Bit-width masking**: mask at assignment only (widths ∉ {8,16,32,64})
- **eval()/tick()/reset() split**: combinational in `eval()`, register update in `tick()`, initialization in `reset()`
- **Expression translation**: constants as `(uint32_t)42ULL`, signed ops as `(int32_t)` casts, concat as shift+OR chain, slice as `>> lo & mask`
- **Sub-module instantiation**: uses `Design` to resolve input/output port directions

### TODO (Future Phases)

- [ ] Phase 2: Compile generated C++ to shared library (dlopen/FFI)
- [ ] Phase 3: Lean FFI bridge — call eval()/tick()/reset() from Lean
- [ ] Phase 4: Integrate with `Signal.loopMemo` for transparent JIT acceleration

---

## SoC Synthesis (Phase 9)

`#writeVerilogDesign rv32iSoCSynth "verilator/generated_soc.sv"` generates SystemVerilog with 119 registers.
The divider is inlined into the top module (no separate sub-module).

### Generated Output

- **File**: `verilator/generated_soc.sv` (~28k lines)
- **Top module**: `Sparkle_Examples_RV32_SoCVerilog_rv32iSoCSynth`
- **Inputs**: `clk`, `rst`, `_gen_imem_wr_en_0`, `_gen_imem_wr_addr_1[11:0]`, `_gen_imem_wr_data_2[31:0]`, `_gen_dmem_wr_en_3`, `_gen_dmem_wr_addr_4[22:0]`, `_gen_dmem_wr_data_5[31:0]`
- **Output**: `out[191:0]` — packed `{pcReg[191:160], uartValidBV[159:128], prevStoreData[127:96], satpReg[95:64], ptwPteReg[63:32], ptwVaddrReg[31:0]}`
- **Wrapper**: `rv32i_soc_wrapper.sv` adapts packed output to testbench interface

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
2. **Multi-cycle restoring divider** (~34 cycles): Inlined into top module with `divPending`, `divStall`, `divAbort`
3. **Duplicated memory arrays**: `Signal.memory` + `Signal.memoryComboRead` stay in sync via identical writes
4. **Non-synthesizable functions replaced**: `mextCompute` → `mulComputeSignal` + `dividerSignal`; `amoCompute` → `amoComputeSignal`

---

## Completed Phases

### Phase 1: Compiler `memoryComboRead` support — DONE
### Phase 2: 3 bug fixes ported to SoC.lean — DONE
### Phase 3: `rv32iSoCSynth` in SoCVerilog.lean, `#synthesizeVerilog` succeeds — DONE

### Phase 9: Verilator Testing — IN PROGRESS

| # | Task | Status |
|---|------|--------|
| 1 | `#writeVerilogDesign` command in Elab.lean | Done |
| 2 | `lake build Examples.RV32.SoCVerilog` — writes `verilator/generated_soc.sv` | Done |
| 3 | `verilator/rv32i_soc_wrapper.sv` — unpack packed output | Done |
| 4 | `verilator/Makefile` — generated SV + wrapper, `make build` | Done |
| 5 | Verilator compiles generated SV successfully | Done |
| 6 | Firmware test: sections 1-9 match hand-written reference exactly (45 UART words) | Done |
| 7 | Firmware test: section 10 + pass marker (`0xcafe0000`) — ALL 48 UART words, cycle 2904 | Done |
| 8 | Linux boot test (OpenSBI → kernel → UART output) | **In Progress** |

### Compiler Bugs Fixed During Phase 9

| Bug | Fix |
|-----|-----|
| `bundle2` hardcoded wire width to 16 bits | Infer from expression type via `inferHWTypeFromSignal` |
| `Prod.fst` slice assumed equal-width halves (`width * 2 - 1`) | Use `getWireWidth` for actual source wire width |
| Verilog backend: duplicate wire/port declarations | Filter port names from internal wire list |
| Core.lean: complex lambda `(fun f7 => extractLsb' 5 1 f7 == 1#1)` | Split into extract + compare steps |

---

## Current Task: Linux Boot Hang Debugging

### Symptoms

- **Hand-written SV**: Boots Linux 6.6.0 successfully (3944 UART bytes in ~7M cycles)
- **Generated SV**: Hangs at ~1906 UART bytes, PC stuck at 0xC0001C88 (recursive page fault)
- OpenSBI phase works correctly (same output as hand-written)
- Kernel starts, prints banner and initial messages, then hangs

### Root Cause Analysis — Updated 2026-02-28

**`memblock_add` enters but fails to persist memory data → `memblock.memory` stays empty → final SATP switch page table has no kernel mapping → page fault → hang.**

#### SATP switch sequence (3 switches total):

| # | Cycle | SATP value | Page table | PTE[0x300] | Result |
|---|-------|-----------|------------|------------|--------|
| 1 | 2606985 | 0x800805F6 | setup_vm trampoline | 0x201000EF ✓ | OK |
| 2 | 2607006 | 0x80080557 | initial page table | 0x201000EF ✓ | OK |
| 3 | 3329886 | 0x800805F7 | setup_vm_final (swapper_pg_dir) | **0x00000000** ✗ | **CRASH** |

The third SATP switch activates `swapper_pg_dir` which has PTE[0x276] and PTE[0x277] (DTB mapping) but **NO PTE[0x300]** (kernel code mapping). This causes an immediate page fault at PC 0xC0001C88 → infinite recursive page fault → hang.

#### Why PTE[0x300] is missing:

`paging_init()` → `setup_vm_final()` uses `create_pgd_mapping()` which relies on `memblock_alloc()` to allocate page table pages. Since `memblock.memory` is empty (total_size=0), no memory can be allocated, so `swapper_pg_dir` stays mostly empty.

#### Why memblock.memory is empty:

`early_init_dt_add_memory_arch` IS called and correctly clamps:
- base: 0x80000000 → 0x80400000 (phys_offset = kernel load address)
- size: 0x02000000 → 0x01C00000

Then it tail-calls `memblock_add(0x80400000, 0x01C00000)`.

**`memblock_add` enters** (confirmed at cycle 3162213, PC 0xC0153F8C) but `memblock.memory.total_size` remains 0 when checked at cycle 3200000 and later.

The "simple case" in `memblock_add_range.isra.0` (when regions[0].size==0) should write:
```
regions[0].base = base    → DMEM word 0x156166
regions[0].size = size    → DMEM word 0x156167
regions[0].flags = 0      → DMEM word 0x156168
type->total_size = size   → DMEM word 0x156159
```

**Something prevents these stores from completing or persisting.**

#### Disproved hypotheses:

1. ~~TLB eviction by `of_get_flat_dt_prop("hotpluggable")` causes wrong physical address~~ — **DISPROVED**: MMU trace showed NO PTW activity, NO TLB misses between the two trace windows. The code path was actually correct — while loop exits properly after 1 DTB reg entry.
2. ~~DTB parsing reads wrong offset (60-byte shift)~~ — DTB parsing works correctly
3. ~~`memblock_add` never called~~ — It IS called at cycle 3162213
4. ~~`early_init_dt_add_memory_arch` never called~~ — Confirmed executing at C0151258

### Prime Suspect: `holdEX` includes `divStall` in generated SoC but NOT in hand-written SV

**Critical difference found:**

| | Hand-written SV (rv32i_soc.sv:803) | Generated (SoC.lean:995-996) |
|---|---|---|
| `holdEX` | `pendingWriteEn` | `pendingWriteEn \|\| (divStall && !flushOrDelay)` |

The generated SoC includes `divStall` in `holdEX`. Since `suppressEXWB = dTLBMiss || holdEX`, and `prevStoreEn_next = suppressEXWB ? false : idex_memWrite`, **any store in the EX stage during a multi-cycle divide (~34 cycles) gets its `prevStoreEn` killed**.

This is the most likely root cause: if a `sw` instruction in `memblock_add_range` happens to execute while `divStall` is active (e.g., from a prior DIV instruction still in flight), the store will be suppressed.

### Debugging Strategy: Trace Diffing (Co-simulation comparison)

Compare cycle-accurate traces from hand-written (working) and generated (broken) SoC:

1. Add per-cycle trace output: `PC, dmem_we, dmem_addr, dmem_wdata, holdEX, divStall, suppressEXWB`
2. Build both SoCs with same testbench
3. Run both with identical firmware/DTB/payload
4. `diff` the traces around memblock_add (cycle ~3162213)
5. Identify exact cycle where generated SoC diverges (store suppressed)

### Next Steps (TODO)

- [ ] **Implement Trace Diffing** — add unified trace format to tb_soc.cpp, build both SoCs
- [ ] **Confirm `divStall` is active during memblock_add stores** — check if holdEX suppresses prevStoreEn
- [ ] **Fix holdEX in SoC.lean** — remove `divStall` from `holdEX` (match hand-written SV) or fix suppression logic to not kill stores during divStall
- [ ] **Verify** Linux boots on fixed generated SoC
- [ ] **(Future) Formal verification** — prove Store Persistence invariant in Lean: `always (idex_isStore ∧ ¬trap ⟹ eventually (dmem_we ∧ correct_addr))`

### Relevant Verilator signal names

| Signal | Description |
|--------|-------------|
| `_gen_useTranslatedAddr_7683` | Whether TLB-translated address is used |
| `_gen_dTLBMiss_7691` | D-side TLB miss |
| `_gen_effectiveAddr_7684` | Final address after MMU bypass check |
| `_gen_dPhysAddr_7681` | Physical address from TLB |
| `_gen_alu_result_approx_7575` | Raw ALU result (VA for loads/stores) |
| `_gen_dmem_read_addr_7710` | Final 23-bit DMEM word address |
| `_gen_actual_dmem_write_addr_7779` | DMEM write word address |
| `_gen_actual_byte0_we_7784` | Byte 0 write enable |
| `_gen_ptwStateNext_9216` | PTW state next (3-bit) |
| `_gen_ptwReq_9178` | PTW request signal |
| `_gen_stall_8786` | Pipeline stall |
| `_gen_flush_8294` | Flush signal |
| `_gen_suppressEXWB_8849` | Suppress EX/WB writeback |

### Key kernel addresses (from /tmp/linux/vmlinux)

| Function | Virtual Address | Description |
|----------|----------------|-------------|
| `early_init_dt_scan_memory` | 0xC01513A0 | Outer DTB scanning function |
| `early_init_dt_add_memory_arch` | 0xC0151238 | Clamps base/size, tail-calls memblock_add |
| `memblock_add` | 0xC0153F8C | Entry point (stores base/size to stack) |
| `memblock_add_range.isra.0` | 0xC0153D40 | Core logic — simple case writes to regions[0] |
| `setup_vm_final` | (in paging_init) | Creates swapper_pg_dir using memblock_alloc |

### Key DMEM addresses for memblock

| Address | DMEM word | Description |
|---------|-----------|-------------|
| 0xC0158554 (PA 0x80558554) | 0x156155 | memblock struct start |
| 0xC015855C (PA 0x8055855C) | 0x156157 | memblock.memory.cnt |
| 0xC0158560 (PA 0x80558560) | 0x156158 | memblock.memory.max |
| 0xC0158564 (PA 0x80558564) | 0x156159 | memblock.memory.total_size |
| 0xC0158568 (PA 0x80558568) | 0x15615A | memblock.memory.regions (pointer) |
| 0xC0158598 (PA 0x80558598) | 0x156166 | memblock_memory_init_regions[0].base |
| 0xC015859C (PA 0x8055859C) | 0x156167 | memblock_memory_init_regions[0].size |
| 0xC01585A0 (PA 0x805585A0) | 0x156168 | memblock_memory_init_regions[0].flags |

---

## Firmware Test — PASSED

- ALL 48 UART words match hand-written reference byte-for-byte
- All 10 sections pass including `0xcafe0000` pass marker at cycle 2904
- Identical behavior to hand-written SV reference

---

## Future Work

- [ ] Fix memblock_add persistence bug and complete Linux boot on generated SV
- [ ] Debug infrastructure cleanup (remove unused debug ports/traces)
- [ ] Interrupt controller (PLIC)
- [ ] Timer interrupt handling (CLINT timer compare)
- [ ] Instruction cache, branch predictor
- [ ] FPGA synthesis targeting

---

## Build & Test Commands

```bash
# Lean build (SoC simulation)
lake build Examples.RV32.SoC

# Lean build (Verilog synthesis → writes verilator/generated_soc.sv)
lake build Examples.RV32.SoCVerilog

# Verilator build (generated SV + wrapper)
cd verilator && make build

# Verilator build (hand-written SV, reference)
cd verilator && make build-handwritten

# Firmware test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/firmware.hex 500000

# Linux boot test
cd verilator && ./obj_dir/Vrv32i_soc ../firmware/opensbi/boot.hex 10000000 \
    --dram /tmp/opensbi/build/platform/generic/firmware/fw_jump.bin \
    --dtb ../firmware/opensbi/sparkle-soc.dtb \
    --payload /tmp/linux/arch/riscv/boot/Image
```
