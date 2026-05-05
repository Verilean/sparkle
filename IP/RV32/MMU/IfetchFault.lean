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

/-! ## Sequential ptwIsIfetchReg

  ptwIsIfetchReg tracks whether the in-flight PTW is for an
  I-side fetch (vs D-side). It's only updated when the PTW is
  IDLE: starts an I-walk iff `ifetchPTWReq ∧ ¬dTLBMiss`
  (D-side has priority).
-/

/-- ptwIsIfetchReg signal wrapper. -/
def ptwIsIfetchRegSignal {dom : DomainConfig}
    (init : Bool) (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Signal dom Bool)
    : Signal dom Bool :=
  Signal.register init
    (ptwIsIfetchNextSignal ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch)

/-- **PTW Idle + ifetchPTWReq + ¬dTLBMiss at t →
    ptwIsIfetchReg at t+1 = true.** -/
theorem ptwIsIfetchReg_set_on_iwalk {dom : DomainConfig}
    (init : Bool) (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Signal dom Bool) (t : Nat)
    (h_idle : ptwIdle.val t = true)
    (h_ireq : ifetchPTWReq.val t = true)
    (h_no_miss : dTLBMiss.val t = false) :
    (ptwIsIfetchRegSignal init ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch).val (t + 1) =
      true := by
  unfold ptwIsIfetchRegSignal ptwIsIfetchNextSignal
  show (Signal.register init _).val (t + 1) = true
  unfold Signal.mux
  show (if ptwIdle.val t then _ else _) = true
  rw [h_idle]
  -- Reduce to the inner conditional on (ifetchPTWReq &&& ¬dTLBMiss).
  show (if (ifetchPTWReq &&& (~~~dTLBMiss)).val t then _ else _) = true
  show (if (ifetchPTWReq.val t && (!dTLBMiss.val t)) then _ else _) = true
  rw [h_ireq, h_no_miss]
  rfl

/-- **PTW Idle + dTLBMiss at t (D-side priority) →
    ptwIsIfetchReg at t+1 = false.** -/
theorem ptwIsIfetchReg_clear_on_dwalk {dom : DomainConfig}
    (init : Bool) (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Signal dom Bool) (t : Nat)
    (h_idle : ptwIdle.val t = true)
    (h_miss : dTLBMiss.val t = true) :
    (ptwIsIfetchRegSignal init ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch).val (t + 1) =
      false := by
  unfold ptwIsIfetchRegSignal ptwIsIfetchNextSignal
  show (Signal.register init _).val (t + 1) = false
  unfold Signal.mux
  show (if ptwIdle.val t then _ else _) = false
  rw [h_idle]
  show (if (ifetchPTWReq.val t && (!dTLBMiss.val t)) then _ else _) = false
  rw [h_miss]
  -- Goal: (if ifetchPTWReq.val t && false then ... else (Signal.pure false).val t) = false
  cases ifetchPTWReq.val t <;> rfl

/-- **PTW ¬Idle at t (mid-walk) → ptwIsIfetchReg at t+1 = ptwIsIfetch.val t.** -/
theorem ptwIsIfetchReg_hold_when_not_idle {dom : DomainConfig}
    (init : Bool) (ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch : Signal dom Bool) (t : Nat)
    (h_no_idle : ptwIdle.val t = false) :
    (ptwIsIfetchRegSignal init ptwIdle ifetchPTWReq dTLBMiss ptwIsIfetch).val (t + 1) =
      ptwIsIfetch.val t := by
  unfold ptwIsIfetchRegSignal ptwIsIfetchNextSignal
  show (Signal.register init _).val (t + 1) = _
  unfold Signal.mux
  show (if ptwIdle.val t then _ else _) = _
  rw [h_no_idle]
  rfl

/-! ## Sequential ifetchFaultPendingReg

  Cycle-wise statements for the I-side fault pending register.
  Per-arm cases:

    * trap-delivery (`ifetchPageFault`) at t → reg at t+1 = false
    * bypassMMU at t → reg at t+1 = false
    * I-walk fault (`ptwFault ∧ ptwIsIfetch`) at t → reg at t+1 = true
    * else → hold

  Key fact: when the trap is delivered, the ifetchFaultPending
  flag is cleared — preventing a stale fault from re-firing on
  a later cycle. -/

/-- ifetchFaultPendingReg signal wrapper. -/
def ifetchFaultPendingRegSignal {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Signal dom Bool) : Signal dom Bool :=
  Signal.register false
    (ifetchFaultPendingNextSignal ifetchPageFault bypassMMU ptwFault
      ptwIsIfetch ifetchFaultPending)

/-- **Trap-delivery cycle clears ifetchFaultPending.** -/
theorem ifetchFaultPendingReg_clears_on_trap_delivery {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Signal dom Bool) (t : Nat)
    (h_pf : ifetchPageFault.val t = true) :
    (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault
      ptwIsIfetch ifetchFaultPending).val (t + 1) = false := by
  unfold ifetchFaultPendingRegSignal
  show (Signal.register false _).val (t + 1) = false
  show (ifetchFaultPendingNextSignal _ _ _ _ _).val t = false
  unfold ifetchFaultPendingNextSignal Signal.mux
  show (if ifetchPageFault.val t then _ else _) = false
  rw [h_pf]
  rfl

/-- **bypassMMU at t clears ifetchFaultPending at t+1.** -/
theorem ifetchFaultPendingReg_clears_on_bypass {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Signal dom Bool) (t : Nat)
    (h_no_pf : ifetchPageFault.val t = false)
    (h_bypass : bypassMMU.val t = true) :
    (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault
      ptwIsIfetch ifetchFaultPending).val (t + 1) = false := by
  unfold ifetchFaultPendingRegSignal
  show (Signal.register false _).val (t + 1) = false
  show (ifetchFaultPendingNextSignal _ _ _ _ _).val t = false
  unfold ifetchFaultPendingNextSignal Signal.mux
  show (if ifetchPageFault.val t then _ else
    (if bypassMMU.val t then _ else _)) = false
  rw [h_no_pf, h_bypass]
  rfl

/-! ## Cycle-N+2 ifetchFaultPending stays cleared

  The 4-arm priority next-state for ifetchFaultPending is:

    ifetchPageFault → false  (trap delivery)
    bypassMMU       → false  (no MMU)
    ptwFault ∧ ptwIsIfetch → true
    else            → hold

  At cycle N when trap delivery fires (ifetchPageFault=true),
  the register is cleared. At cycle N+1, with no PTW-fault-set
  event, the hold-arm preserves false. -/

/-- **ifetchPageFault at N + no PTW-fault-set event at N+1 →
    ifetchFaultPending at N+2 = false.**

    The "no event" hypothesis at N+1 here is that
    `ptwFault ∧ ptwIsIfetch` does NOT fire (which would re-set
    the pending bit). With ifetchPageFault=false at N+1 and
    bypassMMU=false at N+1, the hold-arm preserves the
    previously-cleared value. -/
theorem ifetchFaultPendingReg_stays_false_at_N_plus_2 {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch : Signal dom Bool) (n : Nat)
    (h_pf_n : ifetchPageFault.val n = true)
    (h_no_pf_n1 : ifetchPageFault.val (n + 1) = false)
    (h_no_bypass_n1 : bypassMMU.val (n + 1) = false)
    (h_no_set_n1 :
      (ptwFault.val (n + 1) && ptwIsIfetch.val (n + 1)) = false) :
    (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault ptwIsIfetch
      (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault ptwIsIfetch
        (Signal.pure false))).val (n + 2) = false := by
  -- Step 1: At cycle N, trap delivery → inner reg at N+1 = false.
  have h_inner_n1 :
    (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault ptwIsIfetch
      (Signal.pure false)).val (n + 1) = false :=
    ifetchFaultPendingReg_clears_on_trap_delivery ifetchPageFault bypassMMU ptwFault
      ptwIsIfetch _ n h_pf_n
  -- Step 2: At cycle N+1, no event → outer reg at N+2 = inner reg at N+1 = false.
  unfold ifetchFaultPendingRegSignal
  show (Signal.register false _).val (n + 2) = false
  show (ifetchFaultPendingNextSignal ifetchPageFault bypassMMU ptwFault ptwIsIfetch _).val
    (n + 1) = false
  unfold ifetchFaultPendingNextSignal Signal.mux
  show (if ifetchPageFault.val (n + 1) then _ else
    (if bypassMMU.val (n + 1) then _ else
      (if (ptwFault &&& ptwIsIfetch).val (n + 1) then _ else _))) = false
  rw [h_no_pf_n1, h_no_bypass_n1]
  -- Reduce the (ptwFault &&& ptwIsIfetch).val (n+1) to Bool-and.
  show (if (Signal.ap (Signal.map (· && ·) ptwFault) ptwIsIfetch).val (n + 1) then _
    else _) = false
  show (if (ptwFault.val (n + 1) && ptwIsIfetch.val (n + 1)) then _ else _) = false
  rw [h_no_set_n1]
  -- Goal: ifetchFaultPending(inner reg).val (n+1) = false.
  exact h_inner_n1

/-! ## LTL forms for IfetchFault cycle-N+1 lemmas -/

/-- **LTL form of `ifetchFaultPendingReg_clears_on_trap_delivery`.** -/
theorem ifetchFaultPendingReg_clears_on_trap_delivery_LTL {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Signal dom Bool) :
    ∀ t, ifetchPageFault.val t = true →
         (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault
           ptwIsIfetch ifetchFaultPending).val (t + 1) = false :=
  fun t => ifetchFaultPendingReg_clears_on_trap_delivery ifetchPageFault bypassMMU
    ptwFault ptwIsIfetch ifetchFaultPending t

/-- **LTL form of `ifetchFaultPendingReg_clears_on_bypass`.** -/
theorem ifetchFaultPendingReg_clears_on_bypass_LTL {dom : DomainConfig}
    (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
     ifetchFaultPending : Signal dom Bool) :
    ∀ t, ifetchPageFault.val t = false → bypassMMU.val t = true →
         (ifetchFaultPendingRegSignal ifetchPageFault bypassMMU ptwFault
           ptwIsIfetch ifetchFaultPending).val (t + 1) = false :=
  fun t => ifetchFaultPendingReg_clears_on_bypass ifetchPageFault bypassMMU
    ptwFault ptwIsIfetch ifetchFaultPending t

end Sparkle.IP.RV32.MMU
