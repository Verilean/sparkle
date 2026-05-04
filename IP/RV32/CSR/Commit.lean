/-
  RV32 CSR write-commit pattern — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`. Two recurring shapes:

    1. **Plain CSR write** (~14 sites in SoC.lean):
       `next = if writeActive then newVal else oldVal`
       Used by mie, mtvec, mscratch, satp, medeleg, mideleg,
       sie, stvec, sscratch, mcounteren, scounteren, ...

    2. **Trap-overridable CSR** (6 sites: mepc, mcause, mtval,
       sepc, scause, stval):
       `next = if trapTo then trapPayload
               else if writeActive then newVal else oldVal`
       The trap-entry value (mtvec target / cause / tval) takes
       priority over a software CSR write that fires the same
       cycle.

  This file captures both patterns as pure functions and proves
  the priority + invariance invariants. The downstream `*Next`
  definitions in `SoC.lean` then become single calls.

  Reference: RISC-V priv spec, Vol II §3.1.18 / §4.1.7 (mcause/scause
  spec on trap entry).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure CSR write-commit functions -/

/-- Plain 2-way CSR write commit: write `newVal` if active, else hold `old`. -/
@[inline] def csrPlainNextPure
    (writeActive : Bool) (newVal old : BitVec 32) : BitVec 32 :=
  if writeActive then newVal else old

/-- Trap-overridable 3-way CSR write commit:
    trap-entry payload > CSR write > hold. -/
@[inline] def csrTrapOverrideNextPure
    (trapTo : Bool) (trapPayload : BitVec 32)
    (writeActive : Bool) (newVal old : BitVec 32) : BitVec 32 :=
  if trapTo then trapPayload
  else if writeActive then newVal
  else old

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- Plain commit: no write → hold. -/
@[simp] theorem csrPlainNext_hold (newVal old : BitVec 32) :
    csrPlainNextPure false newVal old = old := by
  rfl

/-- Plain commit: write fires → newVal. -/
@[simp] theorem csrPlainNext_write (newVal old : BitVec 32) :
    csrPlainNextPure true newVal old = newVal := by
  rfl

/-- Trap-override: trap fires → trap payload (regardless of write). -/
@[simp] theorem csrTrapOverrideNext_trap_priority
    (trapPayload : BitVec 32) (writeActive : Bool) (newVal old : BitVec 32) :
    csrTrapOverrideNextPure true trapPayload writeActive newVal old = trapPayload := by
  rfl

/-- Trap-override: no trap, write fires → newVal. -/
@[simp] theorem csrTrapOverrideNext_write
    (trapPayload newVal old : BitVec 32) :
    csrTrapOverrideNextPure false trapPayload true newVal old = newVal := by
  rfl

/-- Trap-override: no trap, no write → hold. -/
@[simp] theorem csrTrapOverrideNext_hold
    (trapPayload newVal old : BitVec 32) :
    csrTrapOverrideNextPure false trapPayload false newVal old = old := by
  rfl

/-! ## Composite specs -/

/-- Plain commit's truth table. -/
theorem csrPlainNextPure_spec :
    ∀ (writeActive : Bool) (newVal old : BitVec 32),
      csrPlainNextPure writeActive newVal old =
        (if writeActive then newVal else old) := by
  intros; rfl

/-- Trap-override's truth table over Bool^2. -/
theorem csrTrapOverrideNextPure_spec :
    ∀ (trapTo : Bool) (trapPayload : BitVec 32)
      (writeActive : Bool) (newVal old : BitVec 32),
      csrTrapOverrideNextPure trapTo trapPayload writeActive newVal old =
        (if trapTo then trapPayload
         else if writeActive then newVal else old) := by
  intros; rfl

/-- Trap-override agrees with plain commit when no trap fires. -/
theorem csrTrapOverride_no_trap_eq_plain
    (trapPayload : BitVec 32) (writeActive : Bool) (newVal old : BitVec 32) :
    csrTrapOverrideNextPure false trapPayload writeActive newVal old =
      csrPlainNextPure writeActive newVal old := by
  unfold csrTrapOverrideNextPure csrPlainNextPure
  rfl

/-! ## Signal-level wrappers -/

/-- Signal-level plain CSR write commit. -/
def csrPlainNextSignal {dom : DomainConfig}
    (writeActive : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux writeActive newVal old

/-- Signal-level 8-bit "CSR" write commit. Used by UART register files
    (LCR/IER/MCR/SCR/DLL/DLM) which mirror the CSR pattern but at
    byte width. -/
def csrPlainNextSignal8 {dom : DomainConfig}
    (writeActive : Signal dom Bool)
    (newVal old : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux writeActive newVal old

/-- Signal-level trap-overridable CSR write commit. -/
def csrTrapOverrideNextSignal {dom : DomainConfig}
    (trapTo : Signal dom Bool) (trapPayload : Signal dom (BitVec 32))
    (writeActive : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux trapTo trapPayload
    (Signal.mux writeActive newVal old)

/-! ## Cycle-wise equivalences -/

theorem csrPlainNextSignal_eq_pure {dom : DomainConfig}
    (writeActive : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) (t : Nat) :
    (csrPlainNextSignal writeActive newVal old).val t =
      csrPlainNextPure (writeActive.val t) (newVal.val t) (old.val t) := by
  unfold csrPlainNextSignal csrPlainNextPure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h : writeActive.val t <;> simp [h]

theorem csrTrapOverrideNextSignal_eq_pure {dom : DomainConfig}
    (trapTo : Signal dom Bool) (trapPayload : Signal dom (BitVec 32))
    (writeActive : Signal dom Bool)
    (newVal old : Signal dom (BitVec 32)) (t : Nat) :
    (csrTrapOverrideNextSignal trapTo trapPayload writeActive newVal old).val t =
      csrTrapOverrideNextPure (trapTo.val t) (trapPayload.val t)
        (writeActive.val t) (newVal.val t) (old.val t) := by
  unfold csrTrapOverrideNextSignal csrTrapOverrideNextPure
  show (Signal.mux _ _ _).val t = _
  unfold Signal.mux
  cases h_trap : trapTo.val t <;>
  cases h_w : writeActive.val t <;>
    simp [h_trap, h_w]

end Sparkle.IP.RV32.CSR
