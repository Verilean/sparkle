/-
  RV32A LR/SC Reservation — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (commit 568bb68). The reservation
  state is a single Bool plus a 32-bit address; this file isolates the
  *next-state* function for the valid bit and proves the invariants
  required by the RISC-V Atomic extension across traps.

  RISC-V priv spec, Vol II §3.5: a trap (exception or interrupt) MUST
  invalidate any outstanding LR reservation. Our SoC additionally
  invalidates on every SC (whether it succeeded or not), which is also
  spec-compliant.

  Three primitive invariants are stated here as `@[simp] theorem`s and
  closed by `decide` on the finite Bool domain. The Signal-level
  next-state is then defined in terms of the pure function so that any
  rewriting of the signal expression that preserves the pure function
  automatically preserves the invariants.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.AMO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure next-state function -/

/--
  Next-state for `reservationValid`, given the current cycle's control
  signals.

  Inputs:
  - `trap`     : `trap_taken` — any synchronous or asynchronous trap
                 that took effect this cycle.
  - `isLR`     : the EXWB-stage instruction is an LR.W that committed.
  - `isSC`     : the EXWB-stage instruction is an SC.W (regardless of
                 whether it succeeded; SC always clears).
  - `prevValid`: the current value of the `reservationValid` register.

  Priority: trap > LR > SC > hold. This matches the SC-always-clears
  rule (so an SC inside a trap-taken cycle still ends with valid=false,
  consistent with the trap arm) and the spec requirement that LR re-
  arms even if a trap is *not* taken on the same cycle.
-/
@[inline] def resValidNextPure (trap isLR isSC prevValid : Bool) : Bool :=
  if trap then false
  else if isLR then true
  else if isSC then false
  else prevValid

/-! ## Spec invariants — closed by `decide` over Bool⁴

These are the three things we must guarantee, stated as one-liners.
-/

/-- A trap unconditionally invalidates the reservation. -/
@[simp] theorem resValidNext_trap_invalidates
    (isLR isSC prevValid : Bool) :
    resValidNextPure true isLR isSC prevValid = false := by
  revert isLR isSC prevValid; decide

/-- An SC (without trap) always clears the reservation, even if there was
    no prior LR. This is the conservative interpretation of the spec
    (Zalrsc §14.2: "An SC must clear the reservation"). -/
@[simp] theorem resValidNext_sc_clears
    (isLR prevValid : Bool) :
    resValidNextPure false isLR true prevValid = (isLR && true) := by
  -- LR has higher priority than SC in our pipeline, so an instruction
  -- that is somehow flagged as both LR and SC (which shouldn't happen
  -- in practice) is treated as LR. The theorem captures that.
  revert isLR prevValid; decide

/-- An LR (without trap, without simultaneous SC) sets the reservation. -/
@[simp] theorem resValidNext_lr_sets
    (prevValid : Bool) :
    resValidNextPure false true false prevValid = true := by
  revert prevValid; decide

/-- When no trap, no LR, no SC: the reservation is held. -/
@[simp] theorem resValidNext_hold
    (prevValid : Bool) :
    resValidNextPure false false false prevValid = prevValid := by
  revert prevValid; decide

/-! ## Composite spec — every reachable input combination -/

/--
  Exhaustive truth table for `resValidNextPure` — verifies that the
  function matches the full intended specification on every possible
  input. Closed by `decide`.

  This is *the* single statement we want CI to depend on. If any change
  to `resValidNextPure` breaks this, every sub-invariant above is
  potentially compromised.
-/
theorem resValidNextPure_spec :
    ∀ (trap isLR isSC prevValid : Bool),
      resValidNextPure trap isLR isSC prevValid =
        (if trap then false
         else if isLR then true
         else if isSC then false
         else prevValid) := by
  decide

/-! ## Signal-level wrapper

  The Signal version is a cycle-wise lift of the pure function. We
  state and prove that the two are equivalent so callers may interchange
  them.
-/

/-- Signal-level next-state (cycle-wise lift of `resValidNextPure`). -/
def resValidNextSignal {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) : Signal dom Bool :=
  Signal.mux trap (Signal.pure false)
    (Signal.mux isLR (Signal.pure true)
      (Signal.mux isSC (Signal.pure false) prevValid))

/--
  At every time `t`, the Signal version evaluates to the pure function
  applied to the current values of its inputs. This is the bridge that
  lets us reason about the loop body's reservation update in terms of
  `resValidNextPure`.
-/
theorem resValidNextSignal_eq_pure {dom : DomainConfig}
    (trap isLR isSC prevValid : Signal dom Bool) (t : Nat) :
    (resValidNextSignal trap isLR isSC prevValid).val t =
      resValidNextPure (trap.val t) (isLR.val t) (isSC.val t)
        (prevValid.val t) := by
  -- Just unfold both sides; both reduce to nested `if`s on the same
  -- Bool values.
  unfold resValidNextSignal resValidNextPure
  simp [Signal.mux, Signal.pure]

/-! ## Reservation address next-state

  When LR fires, latch the LR's target physical address into
  `reservationAddr`. Otherwise hold (the address only matters
  while the reservation is valid; once invalid, the value
  becomes don't-care).
-/

@[inline] def resAddrNextPure
    (isLR : Bool) (exwb_physAddr reservationAddr : BitVec 32) : BitVec 32 :=
  if isLR then exwb_physAddr else reservationAddr

@[simp] theorem resAddrNext_LR
    (exwb_physAddr reservationAddr : BitVec 32) :
    resAddrNextPure true exwb_physAddr reservationAddr = exwb_physAddr := rfl

@[simp] theorem resAddrNext_hold
    (exwb_physAddr reservationAddr : BitVec 32) :
    resAddrNextPure false exwb_physAddr reservationAddr = reservationAddr := rfl

theorem resAddrNextPure_spec
    (isLR : Bool) (exwb_physAddr reservationAddr : BitVec 32) :
    resAddrNextPure isLR exwb_physAddr reservationAddr =
      (if isLR then exwb_physAddr else reservationAddr) := rfl

def resAddrNextSignal {dom : DomainConfig}
    (isLR : Signal dom Bool)
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux isLR exwb_physAddr reservationAddr

/-! ## Sequential resAddrReg: capture-or-hold

  When LR fires at cycle t, resAddrReg at t+1 latches the LR's
  target PA. Otherwise, it holds. -/

/-- resAddrReg signal wrapper. -/
def resAddrRegSignal {dom : DomainConfig}
    (init : BitVec 32) (isLR : Signal dom Bool)
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.register init (resAddrNextSignal isLR exwb_physAddr reservationAddr)

/-- **LR at t → resAddrReg at t+1 = exwb_physAddr.val t.** -/
theorem resAddrReg_latch_on_LR {dom : DomainConfig}
    (init : BitVec 32) (isLR : Signal dom Bool)
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32)) (t : Nat)
    (h_LR : isLR.val t = true) :
    (resAddrRegSignal init isLR exwb_physAddr reservationAddr).val (t + 1) =
      exwb_physAddr.val t := by
  unfold resAddrRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (resAddrNextSignal isLR exwb_physAddr reservationAddr).val t = _
  unfold resAddrNextSignal Signal.mux
  show (if isLR.val t then _ else _) = _
  rw [h_LR]
  rfl

/-- **¬LR at t → resAddrReg at t+1 = reservationAddr.val t.** -/
theorem resAddrReg_hold_when_no_LR {dom : DomainConfig}
    (init : BitVec 32) (isLR : Signal dom Bool)
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32)) (t : Nat)
    (h_no_LR : isLR.val t = false) :
    (resAddrRegSignal init isLR exwb_physAddr reservationAddr).val (t + 1) =
      reservationAddr.val t := by
  unfold resAddrRegSignal
  show (Signal.register init _).val (t + 1) = _
  show (resAddrNextSignal isLR exwb_physAddr reservationAddr).val t = _
  unfold resAddrNextSignal Signal.mux
  show (if isLR.val t then _ else _) = _
  rw [h_no_LR]
  rfl

/-! ## LTL forms -/

theorem resAddrReg_latch_on_LR_LTL {dom : DomainConfig}
    (init : BitVec 32) (isLR : Signal dom Bool)
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32)) :
    ∀ t, isLR.val t = true →
         (resAddrRegSignal init isLR exwb_physAddr reservationAddr).val (t + 1) =
           exwb_physAddr.val t :=
  fun t => resAddrReg_latch_on_LR init isLR exwb_physAddr reservationAddr t

theorem resAddrReg_hold_when_no_LR_LTL {dom : DomainConfig}
    (init : BitVec 32) (isLR : Signal dom Bool)
    (exwb_physAddr reservationAddr : Signal dom (BitVec 32)) :
    ∀ t, isLR.val t = false →
         (resAddrRegSignal init isLR exwb_physAddr reservationAddr).val (t + 1) =
           reservationAddr.val t :=
  fun t => resAddrReg_hold_when_no_LR init isLR exwb_physAddr reservationAddr t

end Sparkle.IP.RV32.AMO
