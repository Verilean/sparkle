/-
  RV32 privilege-mode next-state — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`. The current privilege mode is a
  2-bit field encoding {U=0, S=1, Reserved=2, M=3}. This file isolates
  the next-state function and proves the priv-spec rules:

  * Trap to M-mode → M (3)
  * Trap to S-mode → S (1)
  * MRET → mstatus.MPP
  * SRET → mstatus.SPP (extended to 2 bits via 0#1 ++ spp)
  * Otherwise → hold

  Priority: trap > MRET > SRET > hold. Per RISC-V priv spec, MRET and
  SRET cannot fire on the same cycle (they're distinct opcodes), but
  the priority ordering still matters because flush logic may leave
  both flags asserted briefly during squash. The spec we encode is
  the conservative one matching the loop body's mux chain.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Privilege

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Privilege mode encoding -/

/-- 2-bit privilege mode encoding. -/
def privU : BitVec 2 := 0#2
def privS : BitVec 2 := 1#2
def privM : BitVec 2 := 3#2

/-! ## Pure next-state function -/

/--
  Next-state for `privMode`, given the current cycle's control signals.

  Inputs:
  - `trapToM`  : trap is taken to M-mode this cycle.
  - `trapToS`  : trap is taken to S-mode this cycle. Mutually exclusive
                 with `trapToM`; the loop body computes
                 `trapToM = trap_taken ∧ ¬trapToS`.
  - `isMret`   : the IDEX instruction is an MRET that committed.
  - `isSret`   : the IDEX instruction is an SRET that committed.
  - `mpp`      : current `mstatus.MPP` (2 bits, prior priv before M-trap).
  - `sretPriv` : current `mstatus.SPP` extended to 2 bits via
                 `0#1 ++ spp` (so result is either U=0 or S=1).
  - `priv`     : current `privMode` (held when nothing fires).

  Priority: trapToM > trapToS > isMret > isSret > hold.
-/
@[inline] def privModeNextPure
    (trapToM trapToS isMret isSret : Bool)
    (mpp sretPriv priv : BitVec 2) : BitVec 2 :=
  if trapToM then privM
  else if trapToS then privS
  else if isMret then mpp
  else if isSret then sretPriv
  else priv

/-! ## Spec invariants (decide-closed)

The whole input space is 2⁴ × 4³ = 1024 elements; well within
`decide`'s reach.
-/

/-- Trap to M raises priv to M, regardless of all other signals. -/
@[simp] theorem privModeNext_trapToM
    (trapToS isMret isSret : Bool) (mpp sretPriv priv : BitVec 2) :
    privModeNextPure true trapToS isMret isSret mpp sretPriv priv = privM := by
  revert trapToS isMret isSret mpp sretPriv priv; decide

/-- Trap to S raises priv to S, when no trap-to-M is competing. -/
@[simp] theorem privModeNext_trapToS
    (isMret isSret : Bool) (mpp sretPriv priv : BitVec 2) :
    privModeNextPure false true isMret isSret mpp sretPriv priv = privS := by
  revert isMret isSret mpp sretPriv priv; decide

/-- MRET (when no trap competing) restores priv from MPP. -/
@[simp] theorem privModeNext_mret
    (isSret : Bool) (mpp sretPriv priv : BitVec 2) :
    privModeNextPure false false true isSret mpp sretPriv priv = mpp := by
  revert isSret mpp sretPriv priv; decide

/-- SRET (when no trap nor MRET competing) restores priv from SPP. -/
@[simp] theorem privModeNext_sret
    (mpp sretPriv priv : BitVec 2) :
    privModeNextPure false false false true mpp sretPriv priv = sretPriv := by
  revert mpp sretPriv priv; decide

/-- With no trap, no MRET, no SRET: privilege is held. -/
@[simp] theorem privModeNext_hold
    (mpp sretPriv priv : BitVec 2) :
    privModeNextPure false false false false mpp sretPriv priv = priv := by
  revert mpp sretPriv priv; decide

/-! ## Composite spec -/

/--
  Exhaustive case-table for `privModeNextPure`.
  This is the single statement we want CI to depend on. -/
theorem privModeNextPure_spec :
    ∀ (trapToM trapToS isMret isSret : Bool)
      (mpp sretPriv priv : BitVec 2),
      privModeNextPure trapToM trapToS isMret isSret mpp sretPriv priv =
        (if trapToM then privM
         else if trapToS then privS
         else if isMret then mpp
         else if isSret then sretPriv
         else priv) := by
  decide

/-! ## Signal-level wrapper -/

/-- Signal-level next-state (cycle-wise lift of `privModeNextPure`). -/
def privModeNextSignal {dom : DomainConfig}
    (trapToM trapToS isMret isSret : Signal dom Bool)
    (mpp sretPriv priv : Signal dom (BitVec 2)) : Signal dom (BitVec 2) :=
  Signal.mux trapToM (Signal.pure privM)
    (Signal.mux trapToS (Signal.pure privS)
      (Signal.mux isMret mpp
        (Signal.mux isSret sretPriv priv)))

/--
  Cycle-wise equivalence between Signal and pure versions. This lets
  callers reason about the loop body's privilege transition in terms of
  `privModeNextPure`. -/
theorem privModeNextSignal_eq_pure {dom : DomainConfig}
    (trapToM trapToS isMret isSret : Signal dom Bool)
    (mpp sretPriv priv : Signal dom (BitVec 2)) (t : Nat) :
    (privModeNextSignal trapToM trapToS isMret isSret mpp sretPriv priv).val t =
      privModeNextPure (trapToM.val t) (trapToS.val t)
        (isMret.val t) (isSret.val t)
        (mpp.val t) (sretPriv.val t) (priv.val t) := by
  unfold privModeNextSignal privModeNextPure
  simp [Signal.mux, Signal.pure]

/-! ## Privilege-level comparators

  Trap delegation in `Trap/Delegation.lean` checks whether the
  current privilege is ≤ S — i.e., the trap can be delegated to
  S-mode if `priv ∈ {U, S}` (M cannot delegate to S, because
  M-mode traps stay in M).

  We use the encoding:
    U = 0
    S = 1
    Reserved = 2 (unused)
    M = 3

  So:
    privGtS = priv > 1#2 = priv ∈ {2, 3}
    privLeS = ¬privGtS  = priv ∈ {0, 1}

  Note that priv = 2 (Reserved) is a hardware-impossible value;
  the loop's `privModeNextPure` only assigns U/S/M, so under
  reachable states `privGtS = (priv = M)`. We don't depend on
  that here — the spec is the literal Bool comparator.
-/

/-- privGtS: current priv is greater than S (= M, since 2 is reserved). -/
@[inline] def privGtSPure (priv : BitVec 2) : Bool := 1#2 < priv

/-- privLeS: current priv is ≤ S (= U or S). -/
@[inline] def privLeSPure (priv : BitVec 2) : Bool := !(privGtSPure priv)

/-- privGtS at U: false (0 < 1 is true… wait, this is "greater than", so 0 > 1 = false). -/
@[simp] theorem privGtS_U : privGtSPure 0#2 = false := by decide
@[simp] theorem privGtS_S : privGtSPure 1#2 = false := by decide
@[simp] theorem privGtS_M : privGtSPure 3#2 = true := by decide

@[simp] theorem privLeS_U : privLeSPure 0#2 = true := by decide
@[simp] theorem privLeS_S : privLeSPure 1#2 = true := by decide
@[simp] theorem privLeS_M : privLeSPure 3#2 = false := by decide

/-- Mutual exclusion: privGtS xor privLeS = always true. -/
theorem privGtS_xor_privLeS (priv : BitVec 2) :
    privGtSPure priv ≠ privLeSPure priv := by
  unfold privLeSPure
  cases privGtSPure priv <;> simp

/-! ### Signal-level wrappers -/

def privGtSSignal {dom : DomainConfig}
    (priv : Signal dom (BitVec 2)) : Signal dom Bool :=
  Signal.ult (Signal.pure 1#2) priv

def privLeSSignal {dom : DomainConfig}
    (priv : Signal dom (BitVec 2)) : Signal dom Bool :=
  ~~~(privGtSSignal priv)

end Sparkle.IP.RV32.Privilege
