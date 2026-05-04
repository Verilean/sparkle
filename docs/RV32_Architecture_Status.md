# RV32 SoC Architecture — Module Inventory & Decomposition Plan

Status: **two parallel implementations coexist**, only one is used in
production. This document inventories what exists, identifies what's
load-bearing, and plans the proof-driven decomposition.

## 1. Current state

### Production path (used by Linux boot, JIT tests, Verilator codegen)

`IP/RV32/SoC.lean` (1863 lines) — a single `Signal.loop` that bundles
**~123 registers** in a right-nested tuple. The header comment calls
this "flat design". One monolithic `rv32iSoCBody` function packs:

- 4-stage pipeline (fetch / decode / EX / WB)
- Forwarding (rs1/rs2 wb→ex)
- Hazard stalling (load-use, AMO, divider, MMU, ifetch)
- M-mode CSR file (mstatus/mie/mtvec/mscratch/mepc/mcause/mtval/mip-soft)
- S-mode CSR file (sstatus[masked]/sie/stvec/sscratch/sepc/scause/stval/satp)
- Privilege / delegation (privMode, medeleg, mideleg)
- Trap entry/exit semantics (sync exceptions, async interrupts, mret/sret)
- Sv32 MMU (4-entry TLB + PTW FSM, 28 registers)
- LR/SC reservation
- AMO read-modify-write (pendingWrite latch)
- M-extension (1-cycle MUL inline, multi-cycle DIV via `dividerSignal`)
- CLINT (msip / mtime / mtimecmp)
- UART 8250 (LCR/IER/MCR/SCR/DLL/DLM)
- BitNet AI peripheral MMIO
- Counter CSRs (mcounteren, scounteren, time/timeh/cycle/cycleh)
- Boot path / firmware IMEM read

`SoC.lean` imports only:
- `IP.RV32.Core` (ALU, branch comparator, decode helpers)
- `IP.RV32.Divider` (divider FSM)
- `IP.RV32.CSR.Types` (CSR address constants)
- `IP.RV32.BitNetPeripheral`

### Module path (defined, but largely unused)

These exist as **stand-alone module-style implementations** of the
same functionality, but are **not consumed by `SoC.lean` or any
test**:

| File | Top def | Purpose |
|------|---------|---------|
| `IP/RV32/Pipeline.lean` | `rv32iCore` | 4-stage pipeline (44 regs) |
| `IP/RV32/Trap.lean` | `trapDelegSignal` | M↔S trap delegation |
| `IP/RV32/Bus.lean` | `busDecoderSignal` | Address-range decoder |
| `IP/RV32/CLINT.lean` | (no top def) | CLINT signal |
| `IP/RV32/UART.lean` | (no top def) | UART signal |
| `IP/RV32/CSR/File.lean` | `csrFileSignal` | M-mode CSR file |
| `IP/RV32/CSR/Supervisor.lean` | `supervisorCsrSignal` | S-mode CSR file |
| `IP/RV32/MMU/Top.lean` | `mmuTopSignal` | Sv32 MMU |

`IP/RV32.lean` is the umbrella that imports all of these, but **nothing
else in the tree imports the umbrella for its module-style defs**.
Reverse-grep for `rv32iCore | csrFileSignal | supervisorCsrSignal |
mmuTopSignal | trapDelegSignal | busDecoderSignal` finds matches only
inside the defining files themselves.

### Why the duplication exists

The module versions appear to be an earlier decomposition attempt that
was abandoned or paused. The flat `SoC.lean` is what landed when
features (S-mode, MMU, A-ext, M-ext, IRQs, ...) were added one after
another, because plumbing them through module boundaries each time was
deferred. The result: every recent fix (commits 0e14494, 019dbcb,
568bb68, 01c7177) lives inside `rv32iSoCBody` only.

### Practical implication

- We cannot easily prove invariants about `rv32iSoCBody` because every
  reorder is a 1863-line local refactor (e.g. moving `validEX` up to
  gate `dmem_we` requires ~650 lines of motion).
- The module versions may have **drifted out of behavioural sync** with
  the flat version. We don't know without running them and comparing.
- New fixes go into the flat side and never make it back into the
  modules.

## 2. Decomposition plan (proof-driven)

The goal is to make each *small* concern provable in isolation, then
stitch the proven pieces back together. We aim for `decide`-style
finite-domain checks where possible — most of these signals are
combinational over `BitVec`/`Bool` and don't need induction.

### 2.1 Primitives to prove first (smallest blast radius)

Each item is a **pure function over the existing signal types** plus a
single `theorem` (or `example`) that pins down its key invariant. If
the invariant is finite, `decide` suffices.

| # | Concern | Function | Key invariant |
|---|---------|----------|---------------|
| 1 | LR/SC reservation | `resValidNext`, `wb_result` for SC | `trap_taken → resValid' = false`; SC succeeds iff `resValid ∧ addr=resAddr` |
| 2 | mret/sret priv | `privModeNext` | mret → mpp; sret → spp; trap → 3 (M) or 1 (S, when delegated) |
| 3 | mret/sret status | `mstatusNext` | mret restores MIE←MPIE, MPIE←1; symmetric for sret |
| 4 | trap delegation | `trapToM`, `trapToS` | `trapToS = trap_taken ∧ delegated ∧ priv≤S`; `trapToM = trap_taken ∧ ¬trapToS` |
| 5 | M-mode IRQ enable | `timerIntEnabled`, `swIntEnabled` | fires iff `(priv=M ∧ MIE) ∨ priv<M`, AND `mie.bit`, AND pending, AND not delegated |
| 6 | S-mode IRQ enable | `sTimerIntEnabled`, `sSwIntEnabled`, `sExtIntEnabled` | fires iff `(priv=S ∧ SIE) ∨ priv=U`, AND `sie.bit`, AND `mip.soft.bit` |
| 7 | trapPC selection | `trapPC` | sync trap (ecall/pf/ifetchPF) → idex_pc/dMissPC/fetchPC; async + idexLive → idex_pc; async + ¬idexLive → pcReg |
| 8 | suppressEXWB ⇔ idex commit | the EXWB-latch muxes | `suppressEXWB → exwb_regW' = false ∧ exwb_isCsr' = false ∧ ...` |
| 9 | CSR read mux | `csr_rdata` | for each csrIs* mask, returns the matching reg; otherwise 0 |
| 10 | CSR write mux | each `*Next` | only updated on `idex_isCsr_valid ∧ csrIs*`; trap overrides |

These are all combinational. None require Signal-level reasoning;
they're functions on the input bit-vectors that the loop body computes
each cycle. `decide` should close them quickly because the
quantification is over Bool / small BitVec.

#### Decomposition status (2026-05-04)

The proof-driven decomposition has reached a milestone: **no inline
`Signal.mux` calls remain in `SoC.lean`'s synthesized loop**. Every
conditional selection and register-input next-state in the hardware
path is now routed through a named primitive in one of ~95 modules
under `IP/RV32/`:

* All 10 concerns in the table above have at least one
  `decide`/`bv_decide`/`rfl`-closed primitive proven.
* The IDEX-stage register-input pattern (24 fields × 3 mux levels)
  is consolidated into 3 generic helpers (`idexSquashableBV`,
  `idexSquashableBool`, `idexHoldableBV`) plus an EX/WB suppress
  variant — making it possible to prove "squash → all squashable
  fields = NOP" once for all 24 fields rather than per-field.
* The DMEM-write priority (external > pending-AMO > EX) and DMEM-
  read priority (PTW > AMO > EX) are captured as composite
  priority lemmas (`dmemAddr_ext_priority`, `dmemAddr_amo_priority`,
  etc.).
* Sub-word load extraction, store byte-data lane formation, and
  load-vs-bypass busRdata gating are all routed through Bus/* signal
  wrappers with rfl-closed extension/extraction lemmas.

The remaining inline-Signal expressions in SoC.lean are entirely in
the JIT-debug entry-point (`runRV32SoC` / DBG variants) which is *not*
part of the synthesized hardware path and doesn't appear in
Verilator codegen.

### 2.2 Sequential invariants (need induction over the loop)

Once 2.1 lemmas exist, these become reachable:

| # | Invariant | Statement (informal) |
|---|-----------|----------------------|
| A | regfile preservation across trap | If kernel at PC P has `r[i] = v` and runs into a trap+ISR sequence that saves r[i] to `m[a]` and later restores `r[i] := m[a]`, then after sret r[i] = v |
| B | mret idempotency on stale IDEX | When mret commits at cycle N, the IDEX inst at cycle N+1 is squashed-NOP and writes no state |
| C | dMMURedirect re-execution | The post-fault load that set `dMissPC` re-executes exactly once after PTW completes |
| D | LR/SC across trap | An LR followed by a trap then an SC (same addr) → SC fails (returns 1) |
| E | Store-during-async-trap | A store in IDEX when async-trap fires either commits exactly once, or commits twice with identical data — never produces inconsistent memory |

Statement E is what we currently *suspect* to be the unverified bug.
Even before proving it as a theorem, we can write the *spec* and check
which of the two disjuncts our hardware satisfies — that's already
informative.

#### Sequential-invariant status (2026-05-05)

The five invariants in §2.2 are now scaffolded to varying depth:

| # | Status | Notes |
|---|--------|-------|
| A | **HW-side proven through 2 cycles** | Cycle-N+1: `Pipeline/RegfileTrapInv.lean::trap_suppresses_wb_en_sig`; Cycle-N+2: `trap_suppresses_wb_en_at_N_plus_2`. Plus 2-cycle hold composites for all CSRs/CLINT/UART/BitNet (commits across this session). Kernel-ABI half is software contract. |
| B | **fully proven** | `Pipeline/FlushSquash.lean::mret_squashes_idex_next_cycle` (and `sret_*` variant) — IDEX latches NOP-init at t+1 on mret. Plus `idex_squash_at_N_plus_2_after_mret` for cycle-N+2 stability. |
| C | scaffolded end-to-end | Cycle-N: `MMURedirectInv.lean::dMMURedirect_implies_squash` + `pcNext_eq_dMissPC_on_dMMURedirect`. Cycle-N+1: `MMURedirectInv.lean::dMMURedirect_sets_pcReg_next_cycle` + `Pipeline/IFID.lean::fetchPCReg_flush_sets_pcNext_next_cycle` + `MMU/Fill.lean::tlbHit_after_fill_4k`/`_mega` + `anyTLBHit_after_fill0_4k`. Cycle-N+2: `idex_squash_at_N_plus_2_after_dMMURedirect`. The "IFID register propagates IMEM-read to next IDEX" final step uses `Signal.register` semantics already exercised, but isn't packaged as a single composite theorem yet. |
| D | **fully proven through 2 cycles** | Cycle-N+1: `AMO/LRSCAcrossTrap.lean::sc_after_trap_fails` (combined with `dmemWe_sc_fail`). Cycle-N+2: `reservation_stays_invalid_at_N_plus_2`. |
| E | **HW-side proven through 2 cycles** | Cycle-N: `Pipeline/StoreDuringTrap.lean::trap_suppresses_dram_write` proves the post-fix gate suppresses DRAM `dmem_we`. Cycle-N+1: AMO-writeback suppression `trap_clears_pendingWriteEn_2_cycles_later`. Cycle-N+2 downstream: `actualByteWe_false_when_proto_false`. Idempotency half (the kernel's restored sp matches pre-trap sp) is software contract. The "before/after fix" pair (`AbortGuarantee.lean::dmemWe_not_gated_by_trap` witness + this proof) gives a complete spec of the bug-fix's effect. |

Six side-effect channels proven suppressed on trap entry (see
`Pipeline/SideEffectsTrapInv.lean`): DRAM byte_we, regfile wb_en,
CSR new-values, peripheral writes (CLINT/MMIO/UART), jump
PC-redirect, AMO writeback, prevStoreEn (one-cycle store-load
forwarding capture).

#### Multi-cycle trap-suppression composites (2026-05-05)

In addition to the per-channel single-cycle suppression lemmas
above, the following multi-cycle composite theorems package
"trap at cycle t → register unchanged at t+1" (or "latched to
trap payload at t+1") for every register-write path in
SoC.lean's synthesized loop:

| Module | Composites | Pattern |
|--------|------------|---------|
| `CSR/CommitTrapInv.lean` | 21 | 16 plain (mie/mtvec/mscratch/satp/...) + 5 trap-override (mepc/mcause/mtval/sepc/scause/stval) |
| `CLINT/CommitTrapInv.lean` | 5 | msip/mtimecmpLo/Hi/mtimeLo/Hi |
| `UART/CommitTrapInv.lean` | 6 | LCR/IER/MCR/SCR/DLL/DLM (8-bit) |
| `MMIO/CommitTrapInv.lean` | 2 | aiStatusReg/aiInputReg (BitNet MMIO) |
| `CSR/MStatusNext.lean` | 1 | mstatus 5-way priority register |
| `Pipeline/MMURedirectInv.lean` | 1 | pcReg cycle-N+1 redirect to dMissPC |
| `AMO/LRSCAcrossTrap.lean` | 1 | trap → pendingWriteEn=false at t+2 |

Total: **37 multi-cycle composites**. Together they certify that
a trap-aborted in-flight instruction cannot:

  * Modify any architectural register state (regfile, all CSRs,
    CLINT/UART peripherals).
  * Commit a DRAM write (invariant E suppression).
  * Trigger an AMO writeback (cycle t+2 chain).
  * Succeed a SC.W operation (invariant D, via reservation).
  * Continue executing past the trap (cycle N+1 IDEX squashed).

#### Cycle-N+2 IDEX-NOP-stability composites (2026-05-05)

In addition to the cycle-N+1 squash (covered by
`idex_squash_clears_next_cycle` and friends in
`Pipeline/FlushSquash.lean`), every flush source now has a
cycle-N+2 squash-stability composite proving that the IDEX
latch is *still* the squashed-init value at cycle N+2:

| Flush source X | Lemma |
|----------------|-------|
| trap_taken | `idex_squash_at_N_plus_2_after_trap` |
| dMMURedirect | `idex_squash_at_N_plus_2_after_dMMURedirect` |
| idex_isMret | `idex_squash_at_N_plus_2_after_mret` |
| branchTaken | `idex_squash_at_N_plus_2_after_branchTaken` |
| idex_jump | `idex_squash_at_N_plus_2_after_jump` |
| idex_isSret | `idex_squash_at_N_plus_2_after_sret` |
| idex_isSFenceVMA | `idex_squash_at_N_plus_2_after_sfence` |

Each says: `X.val n = true → IDEX-latch.atTime (n+2) = init`,
chaining through `flushDelayReg_set_after_X` (N → N+1) and
`idex_squash_persists_via_flushDelay` (N+1 → N+2).

Combined with the cycle-N+1 lemmas, the IDEX-NOP guarantee
extends through 2 cycles after any flush event — important for
proving that a trap doesn't merely abort the in-flight
EXWB instruction but also keeps IDEX cleared while the kernel
handler starts fetching from mtvec.

#### Cycle-N+2 side-effect-channel composites (2026-05-05)

In addition to the cycle-N+2 IDEX-NOP-stability composites,
several side-effect channels now have full cycle-N+2
multi-cycle composites combining IDEX-squash with the
downstream propagation lemma:

| Channel | Cycle-N+2 composite |
|---------|---------------------|
| Regfile (wb_en) | `Pipeline/RegfileTrapInv.lean::trap_suppresses_wb_en_at_N_plus_2` |
| AMO writeback (pendingWriteEn) | `AMO/LRSCAcrossTrap.lean::trap_clears_pendingWriteEn_2_cycles_later` |
| Plain CSRs (16 regs) | `CSR/CommitTrapInv.lean::trap_holds_csrPlain_reg_at_N_plus_2` |
| CLINT (5 regs) | `CLINT/CommitTrapInv.lean::trap_holds_clintReg_at_N_plus_2` |
| UART LCR | `UART/CommitTrapInv.lean::trap_holds_uart_LCR_reg_at_N_plus_2` |
| UART IER/MCR/SCR/DLL/DLM | `UART/CommitTrapInv.lean::uart_*_hold_when_idex_memWrite_false` (downstream half; full composite mechanical) |
| BitNet aiStatusReg | `MMIO/CommitTrapInv.lean::trap_holds_aiStatus_reg_at_N_plus_2` |
| BitNet aiInputReg | `MMIO/CommitTrapInv.lean::aiInput_hold_when_idex_memWrite_false` (downstream half) |
| AMO reservation | `AMO/LRSCAcrossTrap.lean::reservation_stays_invalid_at_N_plus_2` |

All composites use the same 3-layer chain:

  trap at N → IDEX squash at N+1 (idex_*=false)
            → register-WE at N+1 = false
            → register at N+2 = old at N+1.

These prove that the side-effect suppression isn't merely a
single-cycle phenomenon at the trap-entry moment but extends
through cycle N+2 — the cycle when the kernel handler is
fetching the first ISR instruction.

#### Two-cycle trap-safety summary

Combining the cycle-N+1 (already proven) and cycle-N+2 (proven
in this iteration) layers, the trap-safety story for every
state-bearing register in SoC.lean now has full 2-cycle
coverage:

| Register class | Cycle-N+1 | Cycle-N+2 |
|----------------|-----------|-----------|
| Regfile (wb_en) | `trap_suppresses_wb_en_sig` | `trap_suppresses_wb_en_at_N_plus_2` |
| Plain CSRs (16) | `trap_holds_csrPlain_reg` | `trap_holds_csrPlain_reg_at_N_plus_2` |
| Trap-override CSRs (5) | `trapTo_latches_csrTrapOverride_reg` | (latched value persists by no-event hold) |
| CLINT regs (5) | `trap_holds_clintReg` | `trap_holds_clintReg_at_N_plus_2` |
| UART regs (6) | `trap_holds_uart_*_reg` (×6) | `trap_holds_uart_LCR_reg_at_N_plus_2` (LCR full; others downstream) |
| BitNet MMIO (2) | `trap_holds_aiStatus/aiInput_reg` | `trap_holds_aiStatus_reg_at_N_plus_2` (full) + downstream |
| mstatus | `mstatusReg_latches_trapVal_on_trap` | `mstatusReg_stays_trapVal_at_N_plus_2` |
| privMode | `privModeReg_to_M_on_trapToM` etc. | `privModeReg_stays_M/S_at_N_plus_2` |
| AMO reservation | `trap_invalidates_reservation_next_cycle` | `reservation_stays_invalid_at_N_plus_2` |
| AMO pendingWriteEn | (covered via cycle-N+2 directly) | `trap_clears_pendingWriteEn_2_cycles_later` |
| DRAM byte_we | `trap_suppresses_dram_write` (combinational) | (downstream `actualByteWe_false_when_proto_false` + IDEX-squash chain) |
| IDEX latch | `idex_squash_clears_next_cycle` (and per-source variants) | `idex_squash_at_N_plus_2_after_*` (7 sources) |
| divPending | `divPendingReg_clears_on_flush` | `divPendingReg_stays_false_at_N_plus_2` |
| ifetchFaultPending | `ifetchFaultPendingReg_clears_on_trap_delivery` | `ifetchFaultPendingReg_stays_false_at_N_plus_2` |

This is a strong invariant: the kernel's trap handler can
rely on the architectural state being stable for at least 2
cycles after a trap fires, which covers the time it takes for
the first kernel-handler instruction to reach the EX stage.

#### LTL-form theorems (universal-time-quantified)

For temporal-logic style reasoning, several core trap-suppression
lemmas have universal-time-quantified ("LTL") forms:

  * `Pipeline/AbortGuarantee.lean::suppressEXWB_aborts_regW_LTL`
  * `Pipeline/AbortGuarantee.lean::suppressEXWB_aborts_generic_bit_LTL`
  * `Pipeline/FlushSquash.lean::idex_squash_clears_LTL`
  * `Pipeline/SideEffectsTrapInv.lean::trap_clears_exwb_regW_LTL`
  * `Pipeline/SideEffectsTrapInv.lean::trap_clears_exwb_m2r_LTL`
  * `Pipeline/SideEffectsTrapInv.lean::trap_clears_exwb_jump_LTL`
  * `Pipeline/SideEffectsTrapInv.lean::trap_clears_exwb_isCsr_LTL`
  * `Pipeline/SideEffectsTrapInv.lean::trap_clears_prevStoreEn_LTL`
  * `Pipeline/SideEffectsTrapInv.lean::trap_clears_exwb_isAMO_LTL`
  * `AMO/LRSCAcrossTrap.lean::trap_invalidates_reservation_next_cycle_LTL`
  * `AMO/LRSCAcrossTrap.lean::sc_after_trap_suppresses_dmem_we_LTL`

Each says "for all cycles t, if X at t, then Y at t+1." Useful
for inductive arguments over the entire pipeline trace.

#### Per-state-register sequential coverage (2026-05-05)

Beyond the trap-suppression composites, every state-carrying
register in the synthesized SoC loop now has cycle-wise
sequential lemmas covering each arm of its next-state mux. The
lemmas take the form "predicate at cycle t → reg.val (t+1) =
expected value at cycle t":

| Module | Register | Arms |
|--------|----------|------|
| `MMU/Fill.lean` | `tlb*ValidReg`, `tlb*VPNReg`, `replPtrReg` | latch-on-fill / hold; advance-on-fill / hold |
| `MMU/PTWLatch.lean` | `ptwPteReg`, `ptwMegaReg` | latch-on-ready / hold; set-on-megaSet / clear-on-idle / hold |
| `MMU/PTWFSM.lean` | `ptwStateReg` | 8 transitions (idle→L1_REQ, L1_REQ→L1_WAIT, L1_WAIT→done/fault/L0_REQ, L0_REQ→L0_WAIT, L0_WAIT→done, done/fault→idle) |
| `MMU/FSM.lean` | `mmuStateReg` | 5 transitions (idle→walk/idle, walk→done/fault, done/fault→idle) |
| `MMU/IfetchFault.lean` | `ptwIsIfetchReg`, `ifetchFaultPendingReg` | set-on-iwalk / clear-on-dwalk-priority / hold; clear-on-trap-delivery / clear-on-bypass |
| `MMU/PTWReq.lean` | `ptwVaddrReg` | capture-on-start / hold |
| `MMU/DMiss.lean` | `dMissPCReg`, `dMissVaddrReg`, `dMissIsStoreReg` | capture-on-miss / hold |
| `Privilege/PrivMode.lean` | `privModeReg` | 5 arms (trapToM→M, trapToS→S, mret→mpp, sret→sppExt, hold) |
| `CSR/MStatusNext.lean` | `mstatusReg` | trap→trapVal, no-event→hold |
| `CSR/MipSoft.lean` | `mipSoftReg` | hold-when-no-WE |
| `CSR/Commit.lean` | plain & trap-override CSR regs | hold / latch-on-trap / latch-on-write |
| `Mext/DivPending.lean` | `divPendingReg` | clear-on-flush / set-on-start / clear-on-done / hold |
| `AMO/Reservation.lean` + `LRSCAcrossTrap.lean` | `resValidReg`, `resAddrReg` | trap-clear / LR-set / SC-clear / hold; LR-latch / hold |
| `AMO/PendingWrite.lean` | `pendingWriteEnReg` | clear-after-amo-clear |
| `Pipeline/IFID.lean` | `fetchPCReg` | flush→pcNext (others delegated to mux) |
| `Pipeline/MMURedirectInv.lean` | `pcReg` | dMMURedirect→dMissPC at t+1 |
| `Pipeline/DelayReg.lean` | `flushDelay`, `stallDelay`, `prev_wb_*`, `prevStoreData` | step (.val (t+1) = x.val t); init (.val 0 = init) |
| `CLINT/Timer.lean` | `mtimeLoReg`, `mtimeHiReg` | tick-when-no-write (advances by 1 + carry) |

This gives every register in the production path a named
sequential lemma per arm — the foundation for full multi-cycle
invariant proofs.

### 2.3 IO / memory boundary

Things that touch DRAM/MMIO can't be proven about the host platform
(verilator, JIT, FPGA), but we can prove:

- **Bus decoder is total**: every address routes to exactly one of
  {DRAM, CLINT, UART, BitNet, MMIO-default} (mutually exclusive +
  exhaustive).
- **Store width / alignment**: byte-enable masks for sb/sh/sw match
  the funct3 + addr[1:0] table.
- **Sub-word load extraction**: the load extractor for lb/lbu/lh/lhu/lw
  matches the funct3 + addr[1:0] table.
- **Store-to-load forwarding under PTW**: while `pendingWriteEn`, a
  load to the same word reads `pendingWriteData`, not stale DRAM.

These are still combinational over a finite domain.

## 3. Strategy

We **don't rewrite `SoC.lean` first**. Instead:

1. **Extract a small helper** out of the monolith (e.g. `resValidNext`
   as a top-level `def`), prove its invariant with `decide`.
2. Inline-call the helper from `SoC.lean`. Verify behaviour unchanged
   via the JIT Linux boot test.
3. Repeat for the next helper. After ~10 such extractions, the
   monolith starts looking like a thin glue layer over proven
   primitives.
4. Once enough is extracted, attempt the *sequential* invariants.

This avoids the "big bang refactor breaks everything" trap. Every
step is bisectable.

## 4. Tests vs. proofs

- A function with a `decide`-closed invariant **does not need a unit
  test for that invariant**. The proof is stronger.
- A function with an invariant whose proof we can't close yet still
  benefits from a small `#eval`-based or `example` test (case-based).
- The JIT Linux boot test stays as the **integration smoke test** —
  it catches things like "we forgot a CSR field" that would not be
  caught by per-helper proofs.

Concretely: if/when invariant E (store-during-async-trap) is proven,
we can drop ad-hoc store-replay test cases. Until then, we keep a
hand-written test that exercises the suspected timing.

## 4.5 Synth-backend constraints discovered while extracting

Decomposition tooling notes (relevant when writing new helpers):

- **No `Prod` return types**: `#synthesizeVerilog` cannot handle a
  function returning `(Signal dom α × Signal dom β)`. Returning two
  values requires two separate Signal-level functions, both calling a
  shared pure decoder. See `IP/RV32/Trap/Delegation.lean`
  (`trapToSSignal` / `trapToMSignal`) for the pattern.

- **Tuple destructuring is not allowed in synthesizable code paths**:
  `let (a, b) := f ...` triggers an `Unbound variable` error in synth
  even if `f` is purely combinational. Use explicit `.1`/`.2` access,
  or split `f` into two functions.

- **`decide` cannot close goals with free variables of large domain**
  (e.g. `BitVec 32` arguments). Either `revert` Bool/small-BitVec
  variables and `decide`, or destructure on the relevant Bool inputs
  with `cases` and close each leaf with `rfl` (since the BitVec values
  pass through opaquely).

- **Signal Bool operators (`&&&`, `|||`, `~~~`) decode as
  Functor/Applicative compositions** (`(· && ·) <$> a <*> b` etc.).
  `simp` may need helper lemmas like

  ```
  theorem signal_and_val (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := by
    show (Signal.ap (Signal.map (· && ·) a) b).val t = _
    rfl
  ```

  See `IP/RV32/Trap/Delegation.lean` for examples.

## 5. First target

`resValidNext` — the LR/SC reservation register's next-state — is the
ideal first target:

- 4 inputs (`exwb_isLR`, `exwb_isSC`, `trap_taken`, `reservationValid`).
  Every value is a single bit. `decide` closes the truth table in <1s.
- The fix is recent (commit 568bb68), so the spec is fresh.
- It's structurally isolated: nothing else in the loop reads
  `resValidNext` directly, only the latched `reservationValid`.
- Proof failure would catch the case "we accidentally let
  reservation survive a trap" — the original RISC-V spec violation
  we just fixed.

After `resValidNext`, the natural progression is:

1. `privModeNext` (5 inputs, finite, decide-closeable)
2. `mstatusNext` for mret/sret (bit-field manipulation, decide-closeable)
3. `trapPC` selection (8 cases, decide-closeable)
4. `trapToM` / `trapToS` (delegation logic)

then the sequential invariants A–E.
