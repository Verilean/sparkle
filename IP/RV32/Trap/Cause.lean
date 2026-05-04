/-
  RV32 trap cause selector — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 1002..1026). Picks the
  trap-cause CSR value (mcause/scause) given the active trap source.

  Two pieces:
    1. `ecallCausePure` — priv-dependent ecall cause:
         U-mode (priv=0)  → cause  8 (ecall from U)
         S-mode (priv=1)  → cause  9 (ecall from S)
         else (priv=3,M)  → cause 11 (ecall from M)
    2. `pageFaultCausePure` — direction-dependent page-fault cause:
         load page fault  → cause 13
         store page fault → cause 15
    3. `trapCausePure` — 8-way priority selector. Priority order
       (MEI omitted as our SoC has no external M-mode IRQ):

         ifetchPageFault → 12 (sync)
         idex_isEcall    → ecallCause (sync)
         pageFault       → pageFaultCause (sync)
         timerIntEn      → 0x80000007 (M-mode timer, async)
         swIntEn         → 0x80000003 (M-mode software, async)
         sExtIntEn       → 0x80000009 (S-mode external, async)
         sSwIntEn        → 0x80000001 (S-mode software, async)
         sTimerIntEn     → 0x80000005 (S-mode timer, async)
         else            → 0 (no trap)

  The MSB of the result is the "is-interrupt" bit — set for the five
  async cases, clear for the three sync cases.

  Reference: RISC-V priv spec, Vol II §3.1.18 (mcause), Table 3.5.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure cause functions -/

/-- ECALL cause: 8 in U, 9 in S, 11 in M. -/
@[inline] def ecallCausePure (privIsU privIsS : Bool) : BitVec 32 :=
  if privIsU then 0x00000008#32
  else if privIsS then 0x00000009#32
  else 0x0000000B#32

/-- Page-fault cause: 13 (load) or 15 (store). -/
@[inline] def pageFaultCausePure (isStoreFault : Bool) : BitVec 32 :=
  if isStoreFault then 0x0000000F#32 else 0x0000000D#32

/-- Eight-way trap-cause priority mux. -/
@[inline] def trapCausePure
    (ifetchPF : Bool)
    (isEcall : Bool) (ecallCause : BitVec 32)
    (pageFault : Bool) (pageFaultCause : BitVec 32)
    (timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn : Bool)
    : BitVec 32 :=
  if ifetchPF then 0x0000000C#32
  else if isEcall then ecallCause
  else if pageFault then pageFaultCause
  else if timerIntEn then 0x80000007#32
  else if swIntEn then 0x80000003#32
  else if sExtIntEn then 0x80000009#32
  else if sSwIntEn then 0x80000001#32
  else if sTimerIntEn then 0x80000005#32
  else 0#32

/-! ## Spec invariants — closed by `decide` over Bool -/

/-- ECALL cause: U-mode is 8. -/
@[simp] theorem ecallCause_U
    (privIsS : Bool) :
    ecallCausePure true privIsS = 0x00000008#32 := by
  rfl

/-- ECALL cause: S-mode is 9. -/
@[simp] theorem ecallCause_S :
    ecallCausePure false true = 0x00000009#32 := by
  rfl

/-- ECALL cause: M-mode (default) is 11. -/
@[simp] theorem ecallCause_M :
    ecallCausePure false false = 0x0000000B#32 := by
  rfl

/-- Page-fault cause: load is 13. -/
@[simp] theorem pageFaultCause_load :
    pageFaultCausePure false = 0x0000000D#32 := by
  rfl

/-- Page-fault cause: store is 15. -/
@[simp] theorem pageFaultCause_store :
    pageFaultCausePure true = 0x0000000F#32 := by
  rfl

/-! ## Trap-cause priority spec -/

/-- ifetch page fault has highest priority: cause = 12. -/
@[simp] theorem trapCause_ifetchPF
    (isEcall : Bool) (ecallCause : BitVec 32)
    (pageFault : Bool) (pageFaultCause : BitVec 32)
    (timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn : Bool) :
    trapCausePure true isEcall ecallCause pageFault pageFaultCause
      timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn = 0x0000000C#32 := by
  rfl

/-- ECALL takes priority over the three page faults below it. -/
@[simp] theorem trapCause_ecall
    (ecallCause : BitVec 32)
    (pageFault : Bool) (pageFaultCause : BitVec 32)
    (timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn : Bool) :
    trapCausePure false true ecallCause pageFault pageFaultCause
      timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn = ecallCause := by
  rfl

/-- D-side page fault takes priority over the five interrupts. -/
@[simp] theorem trapCause_pageFault
    (pageFaultCause : BitVec 32)
    (timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn : Bool) :
    trapCausePure false false 0#32 true pageFaultCause
      timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn = pageFaultCause := by
  rfl

/-- Among interrupts, M-timer has highest priority: cause = 0x80000007. -/
@[simp] theorem trapCause_mTimer
    (swIntEn sExtIntEn sSwIntEn sTimerIntEn : Bool) :
    trapCausePure false false 0#32 false 0#32
      true swIntEn sExtIntEn sSwIntEn sTimerIntEn = 0x80000007#32 := by
  rfl

/-- M-software is next: cause = 0x80000003. -/
@[simp] theorem trapCause_mSw
    (sExtIntEn sSwIntEn sTimerIntEn : Bool) :
    trapCausePure false false 0#32 false 0#32
      false true sExtIntEn sSwIntEn sTimerIntEn = 0x80000003#32 := by
  rfl

/-- S-external follows M-software. -/
@[simp] theorem trapCause_sExt
    (sSwIntEn sTimerIntEn : Bool) :
    trapCausePure false false 0#32 false 0#32
      false false true sSwIntEn sTimerIntEn = 0x80000009#32 := by
  rfl

/-- S-software follows S-external. -/
@[simp] theorem trapCause_sSw
    (sTimerIntEn : Bool) :
    trapCausePure false false 0#32 false 0#32
      false false false true sTimerIntEn = 0x80000001#32 := by
  rfl

/-- S-timer is the lowest-priority interrupt. -/
@[simp] theorem trapCause_sTimer :
    trapCausePure false false 0#32 false 0#32
      false false false false true = 0x80000005#32 := by
  rfl

/-- No trap: cause = 0. -/
@[simp] theorem trapCause_none :
    trapCausePure false false 0#32 false 0#32
      false false false false false = 0#32 := by
  rfl

/-! ## Interrupt-bit invariant

  The MSB (bit 31) of the cause distinguishes interrupts (1) from
  exceptions (0). Below: every async cause has MSB=1, every sync
  cause has MSB=0. -/

/-- The five async causes all have MSB set. -/
theorem mTimer_cause_isInterrupt :
    (0x80000007#32).extractLsb' 31 1 = 1#1 := by decide

theorem mSw_cause_isInterrupt :
    (0x80000003#32).extractLsb' 31 1 = 1#1 := by decide

theorem sExt_cause_isInterrupt :
    (0x80000009#32).extractLsb' 31 1 = 1#1 := by decide

theorem sSw_cause_isInterrupt :
    (0x80000001#32).extractLsb' 31 1 = 1#1 := by decide

theorem sTimer_cause_isInterrupt :
    (0x80000005#32).extractLsb' 31 1 = 1#1 := by decide

/-- The four sync causes all have MSB clear. -/
theorem ifetchPF_cause_notInterrupt :
    (0x0000000C#32).extractLsb' 31 1 = 0#1 := by decide

theorem loadPF_cause_notInterrupt :
    (0x0000000D#32).extractLsb' 31 1 = 0#1 := by decide

theorem storePF_cause_notInterrupt :
    (0x0000000F#32).extractLsb' 31 1 = 0#1 := by decide

theorem ecallU_cause_notInterrupt :
    (0x00000008#32).extractLsb' 31 1 = 0#1 := by decide

theorem ecallS_cause_notInterrupt :
    (0x00000009#32).extractLsb' 31 1 = 0#1 := by decide

theorem ecallM_cause_notInterrupt :
    (0x0000000B#32).extractLsb' 31 1 = 0#1 := by decide

/-! ## Signal-level wrappers -/

/-- Signal-level `ecallCause`. -/
def ecallCauseSignal {dom : DomainConfig}
    (privIsU privIsS : Signal dom Bool) : Signal dom (BitVec 32) :=
  Signal.mux privIsU (Signal.pure 0x00000008#32)
    (Signal.mux privIsS (Signal.pure 0x00000009#32)
      (Signal.pure 0x0000000B#32))

/-- Signal-level `pageFaultCause`. -/
def pageFaultCauseSignal {dom : DomainConfig}
    (isStoreFault : Signal dom Bool) : Signal dom (BitVec 32) :=
  Signal.mux isStoreFault (Signal.pure 0x0000000F#32)
    (Signal.pure 0x0000000D#32)

/-- Signal-level `trapCause` priority mux. -/
def trapCauseSignal {dom : DomainConfig}
    (ifetchPF : Signal dom Bool)
    (isEcall : Signal dom Bool) (ecallCause : Signal dom (BitVec 32))
    (pageFault : Signal dom Bool) (pageFaultCause : Signal dom (BitVec 32))
    (timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn : Signal dom Bool)
    : Signal dom (BitVec 32) :=
  Signal.mux ifetchPF (Signal.pure 0x0000000C#32)
    (Signal.mux isEcall ecallCause
    (Signal.mux pageFault pageFaultCause
    (Signal.mux timerIntEn (Signal.pure 0x80000007#32)
    (Signal.mux swIntEn (Signal.pure 0x80000003#32)
    (Signal.mux sExtIntEn (Signal.pure 0x80000009#32)
    (Signal.mux sSwIntEn (Signal.pure 0x80000001#32)
    (Signal.mux sTimerIntEn (Signal.pure 0x80000005#32)
      (Signal.pure 0#32))))))))

/-! ## Cycle-wise equivalences -/

/-- Helper: `(Signal.pure x).val t = x`. -/
private theorem signal_pure_val {dom : DomainConfig} {α : Type}
    (x : α) (t : Nat) : (Signal.pure (dom := dom) x).val t = x := rfl

/-- `ecallCauseSignal = ecallCausePure`. -/
theorem ecallCauseSignal_eq_pure {dom : DomainConfig}
    (privIsU privIsS : Signal dom Bool) (t : Nat) :
    (ecallCauseSignal privIsU privIsS).val t =
      ecallCausePure (privIsU.val t) (privIsS.val t) := by
  unfold ecallCauseSignal ecallCausePure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h_u : privIsU.val t <;> cases h_s : privIsS.val t <;>
    simp [h_u, h_s, signal_pure_val]

/-- `pageFaultCauseSignal = pageFaultCausePure`. -/
theorem pageFaultCauseSignal_eq_pure {dom : DomainConfig}
    (isStoreFault : Signal dom Bool) (t : Nat) :
    (pageFaultCauseSignal isStoreFault).val t =
      pageFaultCausePure (isStoreFault.val t) := by
  unfold pageFaultCauseSignal pageFaultCausePure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h : isStoreFault.val t <;> simp [h, signal_pure_val]

/-- `trapCauseSignal = trapCausePure` cycle-by-cycle. -/
theorem trapCauseSignal_eq_pure {dom : DomainConfig}
    (ifetchPF : Signal dom Bool)
    (isEcall : Signal dom Bool) (ecallCause : Signal dom (BitVec 32))
    (pageFault : Signal dom Bool) (pageFaultCause : Signal dom (BitVec 32))
    (timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn : Signal dom Bool)
    (t : Nat) :
    (trapCauseSignal ifetchPF isEcall ecallCause pageFault pageFaultCause
       timerIntEn swIntEn sExtIntEn sSwIntEn sTimerIntEn).val t =
      trapCausePure (ifetchPF.val t)
        (isEcall.val t) (ecallCause.val t)
        (pageFault.val t) (pageFaultCause.val t)
        (timerIntEn.val t) (swIntEn.val t) (sExtIntEn.val t)
        (sSwIntEn.val t) (sTimerIntEn.val t) := by
  unfold trapCauseSignal trapCausePure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h_if : ifetchPF.val t <;>
  cases h_ec : isEcall.val t <;>
  cases h_pf : pageFault.val t <;>
  cases h_mt : timerIntEn.val t <;>
  cases h_ms : swIntEn.val t <;>
  cases h_se : sExtIntEn.val t <;>
  cases h_ss : sSwIntEn.val t <;>
  cases h_st : sTimerIntEn.val t <;>
    simp [h_if, h_ec, h_pf, h_mt, h_ms, h_se, h_ss, h_st, signal_pure_val]

end Sparkle.IP.RV32.Trap
