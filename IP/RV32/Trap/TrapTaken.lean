/-
  RV32 trap_taken — the top-level "is some trap firing this cycle"
  predicate, plus its decomposition into M/S-mode interrupts.

  Extracted from `IP/RV32/SoC.lean`. The `trap_taken` Bool drives
  every trap-related signal:
    * mstatus update path (via mstatusNext selector)
    * pc redirect (mtvec/stvec selection)
    * EX/WB suppression (via suppressEXWB)
    * mepc/sepc save (via trapPC)

  Spec:
      anyInt   = mTimerIntEn ∨ mSwIntEn ∨ sTimerIntEn ∨ sSwIntEn ∨ sExtIntEn
      trap_taken = ifetchPageFault ∨ idex_isEcall ∨ pageFault ∨ anyInt

  This is the natural composition of the per-source enable bits.
  We capture it as a pure function so:
    1. The two call sites in `SoC.lean` (the early-block hoist and
       the main flow) share a single Lean object.
    2. Future invariant-proofs over async-vs-sync trap flow can
       refer to a single proven decomposition.

  Note that this file does NOT capture the priority order between
  the four sources — that lives in `Trap/Cause.lean` with the
  cause-mux. Here we only certify that the *disjunction* fires iff
  any source fires.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure predicates -/

/-- All five interrupt-enable bits OR'd together. -/
@[inline] def anyIntPure
    (mTimerIntEn mSwIntEn sTimerIntEn sSwIntEn sExtIntEn : Bool) : Bool :=
  mTimerIntEn || mSwIntEn || sTimerIntEn || sSwIntEn || sExtIntEn

/-- Top-level trap-firing predicate.

    `trap_taken = ifetchPF ∨ ecall ∨ pageFault ∨ anyInt`. -/
@[inline] def trapTakenPure
    (ifetchPF isEcall pageFault : Bool)
    (mTimerIntEn mSwIntEn sTimerIntEn sSwIntEn sExtIntEn : Bool) : Bool :=
  ifetchPF || isEcall || pageFault
    || anyIntPure mTimerIntEn mSwIntEn sTimerIntEn sSwIntEn sExtIntEn

/-! ## Spec invariants — closed by `decide` -/

/-- A non-trap cycle is one where every source is clear. -/
@[simp] theorem trap_taken_quiescent :
    trapTakenPure false false false false false false false false = false := by
  rfl

/-- ifetch page fault always fires `trap_taken`. -/
@[simp] theorem trap_taken_ifetchPF
    (isEcall pageFault mT mS sT sSw sE : Bool) :
    trapTakenPure true isEcall pageFault mT mS sT sSw sE = true := by
  revert isEcall pageFault mT mS sT sSw sE; decide

/-- ecall always fires `trap_taken`. -/
@[simp] theorem trap_taken_ecall
    (ifetchPF pageFault mT mS sT sSw sE : Bool) :
    trapTakenPure ifetchPF true pageFault mT mS sT sSw sE = true := by
  revert ifetchPF pageFault mT mS sT sSw sE; decide

/-- D-side page fault always fires `trap_taken`. -/
@[simp] theorem trap_taken_pageFault
    (ifetchPF isEcall mT mS sT sSw sE : Bool) :
    trapTakenPure ifetchPF isEcall true mT mS sT sSw sE = true := by
  revert ifetchPF isEcall mT mS sT sSw sE; decide

/-- Any of the five interrupts fires `trap_taken`. -/
theorem trap_taken_any_interrupt
    (ifetchPF isEcall pageFault : Bool)
    (mT mS sT sSw sE : Bool) :
    anyIntPure mT mS sT sSw sE = true →
    trapTakenPure ifetchPF isEcall pageFault mT mS sT sSw sE = true := by
  intro h
  unfold trapTakenPure
  rw [h]
  cases ifetchPF <;> cases isEcall <;> cases pageFault <;> rfl

/-! ## Composite spec — exhaustive truth table -/

/-- `trap_taken` matches its full disjunction over Bool^8 (256 cases). -/
theorem trapTakenPure_spec :
    ∀ (ifetchPF isEcall pageFault mT mS sT sSw sE : Bool),
      trapTakenPure ifetchPF isEcall pageFault mT mS sT sSw sE
        = (ifetchPF || isEcall || pageFault || mT || mS || sT || sSw || sE) := by
  decide

/-- `anyInt` matches its disjunction. -/
theorem anyIntPure_spec :
    ∀ (mT mS sT sSw sE : Bool),
      anyIntPure mT mS sT sSw sE = (mT || mS || sT || sSw || sE) := by
  decide

/-! ## Signal-level wrappers -/

/-- Signal-level `anyInt`. -/
def anyIntSignal {dom : DomainConfig}
    (mTimerIntEn mSwIntEn sTimerIntEn sSwIntEn sExtIntEn : Signal dom Bool)
    : Signal dom Bool :=
  mTimerIntEn ||| mSwIntEn ||| sTimerIntEn ||| sSwIntEn ||| sExtIntEn

/-- Signal-level `trap_taken`. Matches the SoC.lean expression
    `((isEcall ||| pageFault) ||| anyInt) ||| ifetchPF` modulo
    associativity. -/
def trapTakenSignal {dom : DomainConfig}
    (ifetchPF isEcall pageFault : Signal dom Bool)
    (mTimerIntEn mSwIntEn sTimerIntEn sSwIntEn sExtIntEn : Signal dom Bool)
    : Signal dom Bool :=
  ifetchPF ||| isEcall ||| pageFault
    ||| anyIntSignal mTimerIntEn mSwIntEn sTimerIntEn sSwIntEn sExtIntEn

/-! ## Cycle-wise equivalence -/

private theorem signal_or_val {dom : DomainConfig}
    (a b : Signal dom Bool) (t : Nat) :
    (a ||| b).val t = (a.val t || b.val t) := by
  show (Signal.ap (Signal.map (· || ·) a) b).val t = _
  rfl

/-- `anyIntSignal = anyIntPure` cycle-by-cycle. -/
theorem anyIntSignal_eq_pure {dom : DomainConfig}
    (mT mS sT sSw sE : Signal dom Bool) (t : Nat) :
    (anyIntSignal mT mS sT sSw sE).val t =
      anyIntPure (mT.val t) (mS.val t) (sT.val t) (sSw.val t) (sE.val t) := by
  unfold anyIntSignal anyIntPure
  simp [signal_or_val, Bool.or_assoc]

/-- `trapTakenSignal = trapTakenPure` cycle-by-cycle. -/
theorem trapTakenSignal_eq_pure {dom : DomainConfig}
    (ifetchPF isEcall pageFault : Signal dom Bool)
    (mT mS sT sSw sE : Signal dom Bool) (t : Nat) :
    (trapTakenSignal ifetchPF isEcall pageFault mT mS sT sSw sE).val t =
      trapTakenPure (ifetchPF.val t) (isEcall.val t) (pageFault.val t)
        (mT.val t) (mS.val t) (sT.val t) (sSw.val t) (sE.val t) := by
  unfold trapTakenSignal trapTakenPure
  simp [signal_or_val, anyIntSignal, anyIntPure, Bool.or_assoc]

end Sparkle.IP.RV32.Trap
