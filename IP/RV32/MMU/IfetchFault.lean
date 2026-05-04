/-
  RV32 I-side page-fault pending tracking — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1713..1722). Two
  state-bit next-functions that together implement the I-side
  page-fault pending tracking:

    1. `ptwIsIfetch` — true while PTW is currently serving an
       instruction-fetch translation (vs. data fetch).
    2. `ifetchFaultPending` — true after PTW faulted on an ifetch
       (latched until trap delivery clears it).

  Spec (per RISC-V priv §4.4 / §3.1.20 instruction page fault):

      ptwIsIfetchNext =
        if ptwIdle then
          if (ifetchPTWReq ∧ ¬dTLBMiss) then true else false
        else
          ptwIsIfetch    (hold while PTW is busy)

      ifetchFaultPendingNext =
        if ifetchPageFault then false      -- trap delivered, clear
        else if bypassMMU then false       -- M-mode never i-page-faults
        else if (ptwFault ∧ ptwIsIfetch) then true  -- ifetch fault: set
        else ifetchFaultPending             -- hold

  Priority order matters: `ifetchPageFault` clears the pending bit
  *before* a new fault could re-set it (per spec, the trap handler
  is responsible for clearing the cause; the hardware only retains
  the bit until the trap is delivered).

  This file proves:
    * `ptwIdle` is the gate for updating `ptwIsIfetch`.
    * `ifetchPageFault` strictly clears `ifetchFaultPending`.
    * `bypassMMU` (i.e. M-mode or satp.MODE=0) strictly clears.
    * `ptwFault ∧ ptwIsIfetch` strictly sets.
    * Otherwise: hold.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure ptwIsIfetch next-state -/

/-- ptwIsIfetch is updated only when PTW is idle: starts an I-side
    walk iff `ifetchPTWReq ∧ ¬dTLBMiss` (the d-side has priority). -/
@[inline] def ptwIsIfetchNextPure
    (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Bool) : Bool :=
  if ptwIdle then
    ifetchPTWReq && !dTLBMiss
  else
    ptwIsIfetch

/-! ## Pure ifetchFaultPending next-state -/

/-- 4-way priority for ifetchFaultPending's next state. -/
@[inline] def ifetchFaultPendingNextPure
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Bool) : Bool :=
  if ifetchPageFault then false
  else if bypassMMU then false
  else if ptwFault && ptwIsIfetch then true
  else ifetchFaultPending

/-! ## Spec invariants — closed by `decide` -/

/-- Trap delivery clears the pending bit. -/
@[simp] theorem ifetchFault_trap_clears
    (bypassMMU ptwFault ptwIsIfetch ifetchFaultPending : Bool) :
    ifetchFaultPendingNextPure true bypassMMU ptwFault ptwIsIfetch
      ifetchFaultPending = false := by
  rfl

/-- bypassMMU clears the pending bit (M-mode or satp.MODE=0). -/
@[simp] theorem ifetchFault_bypass_clears
    (ptwFault ptwIsIfetch ifetchFaultPending : Bool) :
    ifetchFaultPendingNextPure false true ptwFault ptwIsIfetch
      ifetchFaultPending = false := by
  rfl

/-- A fresh PTW fault on an i-side walk sets the pending bit. -/
@[simp] theorem ifetchFault_ptw_fault_sets
    (ifetchFaultPending : Bool) :
    ifetchFaultPendingNextPure false false true true
      ifetchFaultPending = true := by
  rfl

/-- Quiescent state: no event → hold. -/
@[simp] theorem ifetchFault_quiescent_hold (ifetchFaultPending : Bool) :
    ifetchFaultPendingNextPure false false false false ifetchFaultPending
      = ifetchFaultPending := by
  rfl

/-- ptwFault on a non-ifetch walk does NOT set ifetch's pending bit. -/
theorem ifetchFault_d_fault_does_not_set
    (ifetchFaultPending : Bool) :
    ifetchFaultPendingNextPure false false true false ifetchFaultPending
      = ifetchFaultPending := by
  rfl

/-- ptwIsIfetch hold when PTW is non-idle. -/
@[simp] theorem ptwIsIfetch_hold_during_walk
    (ifetchPTWReq dTLBMiss ptwIsIfetch : Bool) :
    ptwIsIfetchNextPure false ifetchPTWReq dTLBMiss ptwIsIfetch
      = ptwIsIfetch := by
  rfl

/-- ptwIsIfetch starts an I-walk on idle iff ifetchPTWReq + no dTLBMiss. -/
theorem ptwIsIfetch_start_iwalk
    (ptwIsIfetch : Bool) :
    ptwIsIfetchNextPure true true false ptwIsIfetch = true := by
  rfl

/-- D-side has priority: dTLBMiss inhibits I-walk start. -/
theorem ptwIsIfetch_dwalk_priority
    (ifetchPTWReq ptwIsIfetch : Bool) :
    ptwIsIfetchNextPure true ifetchPTWReq true ptwIsIfetch = false := by
  unfold ptwIsIfetchNextPure
  cases ifetchPTWReq <;> simp

/-! ## Composite specs -/

theorem ptwIsIfetchNextPure_spec :
    ∀ (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Bool),
      ptwIsIfetchNextPure ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch =
        (if ptwIdle then ifetchPTWReq && !dTLBMiss else ptwIsIfetch) := by
  intros; rfl

theorem ifetchFaultPendingNextPure_spec :
    ∀ (ifetchPageFault bypassMMU ptwFault ptwIsIfetch ifetchFaultPending : Bool),
      ifetchFaultPendingNextPure ifetchPageFault bypassMMU ptwFault
        ptwIsIfetch ifetchFaultPending =
        (if ifetchPageFault then false
         else if bypassMMU then false
         else if ptwFault && ptwIsIfetch then true
         else ifetchFaultPending) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def ptwIsIfetchNextSignal {dom : DomainConfig}
    (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Signal dom Bool)
    : Signal dom Bool :=
  Signal.mux ptwIdle
    (Signal.mux (ifetchPTWReq &&& (~~~dTLBMiss))
      (Signal.pure true) (Signal.pure false))
    ptwIsIfetch

def ifetchFaultPendingNextSignal {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Signal dom Bool) : Signal dom Bool :=
  Signal.mux ifetchPageFault (Signal.pure false)
    (Signal.mux bypassMMU (Signal.pure false)
      (Signal.mux (ptwFault &&& ptwIsIfetch) (Signal.pure true)
        ifetchFaultPending))

end Sparkle.IP.RV32.MMU
