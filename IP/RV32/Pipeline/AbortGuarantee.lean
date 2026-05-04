/-
  RV32 EX/WB abort guarantee — sequential invariant (LTL)

  This is the first **sequential** (time-stepping) proof in the
  decomposition effort, building on the pure helpers extracted
  in commits 40f51e5 ... a70d809.

  Goal: when `suppressEXWB` fires at cycle t, the corresponding
  EXWB control bits are all `false` at cycle t+1, so the in-flight
  IDEX instruction does not commit.

  This is the cornerstone of trap correctness: every trap-related
  fix in the recent commits (568bb68, 0e14494, 019dbcb, 01c7177)
  rests on this property holding.

  We use the `register` primitive's semantics directly:

      (Signal.register init input).val 0       = init
      (Signal.register init input).val (n + 1) = input.val n

  Combined with the latch expression in the loop body
  (`mux suppressEXWB false idex_regWrite`), the next-cycle property
  follows by case analysis on `suppressEXWB.val t`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Verification.Temporal
import IP.RV32.Pipeline.SuppressEXWB

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Temporal

/-!
## The latched EXWB control bit, modeled as a Signal

  `exwbRegWNextSignal` — the value driving the EXWB regWrite latch's
  input. This is exactly the expression
  `mux suppressEXWB false idex_regWrite` from `SoC.lean` (line 1594).
-/

/-- Next-state for the EXWB regWrite latch. -/
def exwbRegWNextSignal {dom : DomainConfig}
    (suppressEXWB idex_regWrite : Signal dom Bool) : Signal dom Bool :=
  Signal.mux suppressEXWB (Signal.pure false) idex_regWrite

/-- The latched EXWB regWrite signal as a register chain. The initial
    value at t=0 is `false`. -/
def exwbRegWSignal {dom : DomainConfig}
    (suppressEXWB idex_regWrite : Signal dom Bool) : Signal dom Bool :=
  Signal.register false (exwbRegWNextSignal suppressEXWB idex_regWrite)

/-!
## The abort guarantee — sequential invariant
-/

/--
  **Abort guarantee for register write.**

  If `suppressEXWB` is asserted at cycle `t`, the EXWB regWrite latch
  is `false` at cycle `t+1`. Equivalently: a suppressed instruction's
  register write is dropped, exactly one cycle later.

  This is invariant E0 from the proof effort: the smallest sequential
  property we need to certify trap correctness. -/
theorem suppressEXWB_aborts_regW_next_cycle {dom : DomainConfig}
    (suppressEXWB idex_regWrite : Signal dom Bool) (t : Nat) :
    suppressEXWB.atTime t = true →
    (exwbRegWSignal suppressEXWB idex_regWrite).atTime (t + 1) = false := by
  intro h_supp
  -- Unfold the register and next-state definitions.
  unfold exwbRegWSignal exwbRegWNextSignal
  -- (register false ...).val (t+1) = ((mux suppressEXWB false idex_regWrite).val t)
  show (Signal.register false _).atTime (t + 1) = false
  unfold Signal.atTime
  show (Signal.register false _).val (t + 1) = false
  -- register's semantics give us the next-state value:
  show (Signal.mux suppressEXWB (Signal.pure false) idex_regWrite).val t = false
  -- mux semantics: if suppressEXWB.val t then (pure false).val t else ...
  unfold Signal.mux
  -- Now goal is: if suppressEXWB.val t then (pure false).val t else idex_regWrite.val t = false
  -- We have h_supp : suppressEXWB.atTime t = true
  -- atTime = val
  show (if suppressEXWB.val t then _ else _) = false
  rw [show suppressEXWB.val t = true from h_supp]
  rfl

/--
  Same but for the temporal `next` operator: an LTL-style statement.
  Reads as: "If `suppressEXWB`, then in the next cycle, EXWB regWrite
  is not asserted." -/
theorem suppressEXWB_aborts_regW_LTL {dom : DomainConfig}
    (suppressEXWB idex_regWrite : Signal dom Bool) :
    ∀ t, suppressEXWB.atTime t = true →
         (exwbRegWSignal suppressEXWB idex_regWrite).atTime (t + 1) = false :=
  fun t => suppressEXWB_aborts_regW_next_cycle suppressEXWB idex_regWrite t

/-!
## Generalising to all gated EXWB control bits

  The same pattern applies to `exwb_m2r`, `exwb_jump`, `exwb_isCsr`,
  `prevStoreEn` (memWrite), and `exwb_isAMO`. They all use
  `Signal.mux suppressEXWB (Signal.pure false) idex_*` for next-state.

  We package this generically: any latch driven by
  `mux suppressEXWB false x` is `false` one cycle after `suppressEXWB`. -/

/-- Generic helper: any next-state of the form
    `mux suppressEXWB false x` produces `false` at cycle t+1 when
    `suppressEXWB` is asserted at cycle t. -/
theorem suppressEXWB_aborts_generic_bit {dom : DomainConfig}
    (suppressEXWB ctrl_bit : Signal dom Bool) (t : Nat) :
    suppressEXWB.atTime t = true →
    (Signal.register false
      (Signal.mux suppressEXWB (Signal.pure false) ctrl_bit)).atTime (t + 1) = false := by
  intro h_supp
  unfold Signal.atTime
  show (Signal.register false (Signal.mux suppressEXWB
    (Signal.pure false) ctrl_bit)).val (t + 1) = false
  show (Signal.mux suppressEXWB (Signal.pure false) ctrl_bit).val t = false
  unfold Signal.mux
  show (if suppressEXWB.val t then _ else _) = false
  rw [show suppressEXWB.val t = true from h_supp]
  rfl

/-!
## DRAM-write non-suppression — the open suspect, made formal

The peripheral writes (CLINT/MMIO/UART) all gate on `validEX`:

    clintWE = idex_memWrite ∧ isCLINT_ex ∧ validEX
    mmioWE  = idex_memWrite ∧ is_mmio_ex ∧ validEX
    uartWE  = idex_memWrite ∧ isUART_ex ∧ validEX

The DRAM write does NOT:

    dmem_we = idex_memWrite ∧ isDMEM_ex ∧ ¬dTLBMiss ∧ ¬scExFails

The next theorem makes this asymmetry **machine-checked**: it
constructs a concrete witness state where `suppressEXWB = true` but
`dmem_we = true`. Such a state is unreachable for the suppressors
that imply `freezeIDEX` (e.g. `pendingWriteEn`, `mmuBusy`) because
those also block `idex_memWrite` from updating — but it IS reachable
for `trap_taken` and `dMMURedirect`, which do not freeze IDEX. -/

/-- The DRAM `dmem_we` expression as a pure function of its
    five Bool inputs. -/
@[inline] def dmemWePure
    (idex_memWrite isDMEM_ex dTLBMiss scExFails : Bool) : Bool :=
  idex_memWrite && isDMEM_ex && !dTLBMiss && !scExFails

/--
  Witness theorem: there exist states where `suppressEXWB = true`
  (specifically: `trap_taken = true`) AND `dmem_we = true` (a normal
  DMEM store is in IDEX with no TLB miss and no SC fail). This means
  the DRAM write commits even though every other side-effect-bearing
  EXWB control bit is suppressed.

  This is the **smoking-gun asymmetry** that the residual Linux boot
  bug is suspected to expose. Proving this theorem here doesn't fix
  the bug — it formalises the gap so any future change must address
  it explicitly. -/
theorem dmemWe_not_gated_by_trap :
    ∃ (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
       idex_memWrite isDMEM_ex scExFails : Bool),
      suppressEXWBPure trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect = true ∧
      dmemWePure idex_memWrite isDMEM_ex dTLBMiss scExFails = true := by
  -- Witness: a normal DMEM store is in IDEX, no TLB miss, no SC fail,
  -- and `trap_taken` fires this cycle. All other suppressors clear.
  refine ⟨true, false, false, false, false, true, true, false, ?_⟩
  decide

/--
  Same witness, but with `dMMURedirect = true` instead of
  `trap_taken`. dMMURedirect is also asserted while IDEX still
  holds the post-load instruction (per fix 0e14494's analysis). -/
theorem dmemWe_not_gated_by_dMMURedirect :
    ∃ (trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect
       idex_memWrite isDMEM_ex scExFails : Bool),
      suppressEXWBPure trap_taken dTLBMiss pendingWriteEn mmuBusy dMMURedirect = true ∧
      dmemWePure idex_memWrite isDMEM_ex dTLBMiss scExFails = true := by
  refine ⟨false, false, false, false, true, true, true, false, ?_⟩
  decide

/-!
## Connection to invariant E

This file establishes the **single-cycle abort guarantee**: when
`suppressEXWB` fires, every gated EXWB control bit is dropped one
cycle later.

The full invariant E (`docs/RV32_Architecture_Status.md` §2.2)
adds two more pieces, both still TODO:

  E1. **Re-execution after sret**: when mepc points back to the
      suppressed instruction's PC, that instruction re-fetches and
      re-executes with stable inputs (regfile values are the same as
      pre-trap because trap entry/exit save/restore them).

  E2. **DRAM-write asymmetry**: the DRAM `dmem_we` does NOT use
      `validEX` gating, so a store in IDEX during a trap commits to
      DRAM even though `suppressEXWB` would otherwise drop it. This
      is the open question that motivated this file.

E1 requires modeling the trap save/restore sequence (kernel ABI).
E2 requires showing the dmem_we's actual gating is sufficient — i.e.
either prove the double-commit is benign (idempotent) or prove the
gating is missing (the latter would be the long-suspected bug).

Both are larger proofs and depend on this single-cycle abort
guarantee as a building block. -/

end Sparkle.IP.RV32.Pipeline
