/-
  RV32 TLB fill + replacement-pointer logic — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1654..1694). After the
  PTW completes a translation, the resulting PTE is installed into
  the TLB at the entry pointed to by `replPtrReg`. The
  replacement-pointer is then incremented (round-robin policy).

  Spec:

    replIsN(N : 2-bit)  = (replPtrReg == N)
    doFillN             = tlbFill ∧ replIsN
    tlb_validNext       = if sfenceVMA then false        -- TLB invalidate
                          else if doFillN then true       -- mark valid
                          else tlb_valid                  -- hold
    tlb_VPN/PPN/FlagsNext = if doFillN then fillVal else hold
    replPtrNext         = if tlbFill then replPtr + 1 else replPtr

  Per-entry mutual exclusion: at most one of {doFill0, doFill1,
  doFill2, doFill3} fires per cycle (since replPtrReg picks
  exactly one entry).

  This file proves:
    * Per-entry doFill characterization.
    * Replacement-pointer round-robin invariant.
    * sfenceVMA always clears valid.
    * doFill always sets valid.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Per-entry replacement-pointer match -/

@[inline] def replIs0Pure (replPtr : BitVec 2) : Bool := replPtr == 0#2
@[inline] def replIs1Pure (replPtr : BitVec 2) : Bool := replPtr == 1#2
@[inline] def replIs2Pure (replPtr : BitVec 2) : Bool := replPtr == 2#2
@[inline] def replIs3Pure (replPtr : BitVec 2) : Bool := replPtr == 3#2

/-- Per-entry fill enable: tlbFill && match. -/
@[inline] def doFillNPure (tlbFill : Bool) (replIsN : Bool) : Bool :=
  tlbFill && replIsN

/-- Replacement pointer next: increment on fill, hold otherwise. -/
@[inline] def replPtrNextPure (tlbFill : Bool) (replPtr : BitVec 2) : BitVec 2 :=
  if tlbFill then replPtr + 1#2 else replPtr

/-! ## Per-entry valid bit next-state

  Spec:
    sfenceVMA → false  (full TLB invalidate)
    doFillN   → true   (entry just installed)
    else      → hold   (no change)

  Priority: sfenceVMA > doFillN > hold.
-/
@[inline] def tlbValidNextPure
    (sfenceVMA : Bool) (doFillN : Bool) (oldValid : Bool) : Bool :=
  if sfenceVMA then false
  else if doFillN then true
  else oldValid

/-! ## Spec invariants — closed by `decide` over `BitVec 2` (4 cases) -/

/-- Exactly one of replIs0..3 fires for any replPtr. -/
theorem replIs_exactly_one (replPtr : BitVec 2) :
    (if replIs0Pure replPtr then 1 else 0)
      + (if replIs1Pure replPtr then 1 else 0)
      + (if replIs2Pure replPtr then 1 else 0)
      + (if replIs3Pure replPtr then 1 else 0) = 1 := by
  unfold replIs0Pure replIs1Pure replIs2Pure replIs3Pure
  revert replPtr
  decide

/-- doFillN is gated by both tlbFill and the per-entry match. -/
theorem doFill_no_fill (replIsN : Bool) :
    doFillNPure false replIsN = false := by
  unfold doFillNPure
  rfl

theorem doFill_no_match (tlbFill : Bool) :
    doFillNPure tlbFill false = false := by
  unfold doFillNPure
  cases tlbFill <;> rfl

theorem doFill_fires :
    doFillNPure true true = true := by rfl

/-- Pairwise mutex: doFill0 and doFill1 can't both fire simultaneously. -/
theorem doFill_mutex_01 (tlbFill : Bool) (replPtr : BitVec 2) :
    !(doFillNPure tlbFill (replIs0Pure replPtr)
       && doFillNPure tlbFill (replIs1Pure replPtr)) = true := by
  unfold doFillNPure replIs0Pure replIs1Pure
  revert tlbFill replPtr; decide

theorem doFill_mutex_02 (tlbFill : Bool) (replPtr : BitVec 2) :
    !(doFillNPure tlbFill (replIs0Pure replPtr)
       && doFillNPure tlbFill (replIs2Pure replPtr)) = true := by
  unfold doFillNPure replIs0Pure replIs2Pure
  revert tlbFill replPtr; decide

theorem doFill_mutex_03 (tlbFill : Bool) (replPtr : BitVec 2) :
    !(doFillNPure tlbFill (replIs0Pure replPtr)
       && doFillNPure tlbFill (replIs3Pure replPtr)) = true := by
  unfold doFillNPure replIs0Pure replIs3Pure
  revert tlbFill replPtr; decide

theorem doFill_mutex_12 (tlbFill : Bool) (replPtr : BitVec 2) :
    !(doFillNPure tlbFill (replIs1Pure replPtr)
       && doFillNPure tlbFill (replIs2Pure replPtr)) = true := by
  unfold doFillNPure replIs1Pure replIs2Pure
  revert tlbFill replPtr; decide

/-! ## Replacement pointer spec -/

/-- No fill → hold. -/
@[simp] theorem replPtrNext_no_fill (replPtr : BitVec 2) :
    replPtrNextPure false replPtr = replPtr := by rfl

/-- Fill → increment (mod 4 due to BitVec 2 wraparound). -/
@[simp] theorem replPtrNext_fill (replPtr : BitVec 2) :
    replPtrNextPure true replPtr = replPtr + 1#2 := by rfl

/-- Round-robin: 0 → 1 → 2 → 3 → 0 → ... -/
theorem replPtr_round_robin (replPtr : BitVec 2) :
    replPtrNextPure true (replPtrNextPure true
      (replPtrNextPure true (replPtrNextPure true replPtr))) = replPtr := by
  unfold replPtrNextPure
  revert replPtr
  decide

/-! ## Valid-bit next-state spec -/

/-- sfenceVMA always clears valid (full TLB flush). -/
@[simp] theorem tlbValidNext_sfence (doFillN oldValid : Bool) :
    tlbValidNextPure true doFillN oldValid = false := by rfl

/-- Fill (no sfence) sets valid. -/
@[simp] theorem tlbValidNext_fill (oldValid : Bool) :
    tlbValidNextPure false true oldValid = true := by rfl

/-- No event → hold. -/
@[simp] theorem tlbValidNext_hold (oldValid : Bool) :
    tlbValidNextPure false false oldValid = oldValid := by rfl

/-! ## Composite specs -/

theorem replPtrNextPure_spec (tlbFill : Bool) (replPtr : BitVec 2) :
    replPtrNextPure tlbFill replPtr =
      (if tlbFill then replPtr + 1#2 else replPtr) := by rfl

theorem tlbValidNextPure_spec (sfenceVMA doFillN oldValid : Bool) :
    tlbValidNextPure sfenceVMA doFillN oldValid =
      (if sfenceVMA then false
       else if doFillN then true
       else oldValid) := by rfl

/-! ## Signal-level wrappers -/

def replIs0Signal {dom : DomainConfig}
    (replPtr : Signal dom (BitVec 2)) : Signal dom Bool :=
  replPtr === 0#2

def replIs1Signal {dom : DomainConfig}
    (replPtr : Signal dom (BitVec 2)) : Signal dom Bool :=
  replPtr === 1#2

def replIs2Signal {dom : DomainConfig}
    (replPtr : Signal dom (BitVec 2)) : Signal dom Bool :=
  replPtr === 2#2

def replIs3Signal {dom : DomainConfig}
    (replPtr : Signal dom (BitVec 2)) : Signal dom Bool :=
  replPtr === 3#2

def doFillNSignal {dom : DomainConfig}
    (tlbFill replIsN : Signal dom Bool) : Signal dom Bool :=
  tlbFill &&& replIsN

def replPtrNextSignal {dom : DomainConfig}
    (tlbFill : Signal dom Bool)
    (replPtr : Signal dom (BitVec 2)) : Signal dom (BitVec 2) :=
  let one : Signal dom (BitVec 2) := Signal.pure 1#2
  Signal.mux tlbFill (replPtr + one) replPtr

def tlbValidNextSignal {dom : DomainConfig}
    (sfenceVMA doFillN oldValid : Signal dom Bool) : Signal dom Bool :=
  Signal.mux sfenceVMA (Signal.pure false)
    (Signal.mux doFillN (Signal.pure true) oldValid)

end Sparkle.IP.RV32.MMU
