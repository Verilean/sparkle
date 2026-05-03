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
