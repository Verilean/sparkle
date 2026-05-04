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
import IP.RV32.MMU.TLB

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

/-! ## Per-entry data-field next-state

  For each TLB entry's data fields (VPN, PPN, Flags, Mega), the
  next-state is a uniform 2-way mux:

    fieldNext = if doFillN then fillVal else hold

  This is the same shape as `csrPlainNextPure` but parameterized
  over the field's bit-width or Bool type.

  We provide a generic pure helper plus four type-specialized
  Signal wrappers (BitVec 20 for VPN, BitVec 22 for PPN, BitVec 8
  for flags, Bool for the megapage flag) — these are the four
  shapes used in SoC.lean's TLB-entry next-state block.
-/

/-- Generic per-field next-state: latch on doFill, hold otherwise. -/
@[inline] def tlbFieldNextPure {α} (doFillN : Bool) (fillVal hold : α) : α :=
  if doFillN then fillVal else hold

/-- doFill → latch. -/
@[simp] theorem tlbFieldNext_latch {α} (fillVal hold : α) :
    tlbFieldNextPure true fillVal hold = fillVal := rfl

/-- ¬doFill → hold. -/
@[simp] theorem tlbFieldNext_hold {α} (fillVal hold : α) :
    tlbFieldNextPure false fillVal hold = hold := rfl

/-- VPN-field next-state Signal wrapper. -/
def tlbVPNNextSignal {dom : DomainConfig}
    (doFillN : Signal dom Bool)
    (fillVPN holdVPN : Signal dom (BitVec 20)) : Signal dom (BitVec 20) :=
  Signal.mux doFillN fillVPN holdVPN

/-- PPN-field next-state Signal wrapper. -/
def tlbPPNNextSignal {dom : DomainConfig}
    (doFillN : Signal dom Bool)
    (fillPPN holdPPN : Signal dom (BitVec 22)) : Signal dom (BitVec 22) :=
  Signal.mux doFillN fillPPN holdPPN

/-- Flags-field next-state Signal wrapper. -/
def tlbFlagsNextSignal {dom : DomainConfig}
    (doFillN : Signal dom Bool)
    (fillFlags holdFlags : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux doFillN fillFlags holdFlags

/-- Mega-flag next-state Signal wrapper. -/
def tlbMegaNextSignal {dom : DomainConfig}
    (doFillN : Signal dom Bool)
    (fillMega holdMega : Signal dom Bool) : Signal dom Bool :=
  Signal.mux doFillN fillMega holdMega

/-! ## Sequential: TLB fill at cycle N → entry valid + VPN matches at cycle N+1

  This is the cornerstone of the multi-cycle invariant C
  (post-fault load re-execution): if the PTW completed at
  cycle N and `doFillN.val N = true` (with no SFENCE.VMA
  competing), then at cycle N+1 the TLB entry holds the new
  fill data and is marked valid.

  Concretely:
    `Signal.register false (tlbValidNextSignal sfenceVMA doFillN tlb_valid)`
    .val (t+1) = true
  whenever `doFillN.val t = true` and `sfenceVMA.val t = false`.

  And:
    `Signal.register init (tlbVPNNextSignal doFillN fillVPN tlb_vpn)`
    .val (t+1) = fillVPN.val t
  whenever `doFillN.val t = true`.

  Together, the entry at cycle N+1 satisfies:
    valid = true ∧ entryVPN = fillVPN
  so a lookup with dVPN = fillVPN at cycle N+1 returns true via
  `tlbHit_valid_match` (in MMU/TLB.lean).
-/

/-- Wrapper: TLB-valid bit register (the persistent entry-valid). -/
def tlbValidRegSignal {dom : DomainConfig}
    (sfenceVMA doFillN tlb_valid : Signal dom Bool) : Signal dom Bool :=
  Signal.register false (tlbValidNextSignal sfenceVMA doFillN tlb_valid)

/-- Wrapper: TLB-VPN field register. -/
def tlbVPNRegSignal {dom : DomainConfig}
    (doFillN : Signal dom Bool)
    (fillVPN tlb_vpn : Signal dom (BitVec 20)) : Signal dom (BitVec 20) :=
  Signal.register 0#20 (tlbVPNNextSignal doFillN fillVPN tlb_vpn)

/-- **TLB-fill propagates valid=true to N+1.** -/
theorem tlbValidReg_set_after_fill {dom : DomainConfig}
    (sfenceVMA doFillN tlb_valid : Signal dom Bool) (t : Nat)
    (h_no_sfence : sfenceVMA.val t = false)
    (h_fill : doFillN.val t = true) :
    (tlbValidRegSignal sfenceVMA doFillN tlb_valid).val (t + 1) = true := by
  unfold tlbValidRegSignal
  show (Signal.register false _).val (t + 1) = true
  -- (register init next).val (t+1) = next.val t
  show (tlbValidNextSignal sfenceVMA doFillN tlb_valid).val t = true
  unfold tlbValidNextSignal Signal.mux
  show (if sfenceVMA.val t = true then _
        else if doFillN.val t = true then (Signal.pure true).val t
        else tlb_valid.val t) = true
  rw [h_no_sfence, h_fill]
  rfl

/-- **TLB-fill propagates fillVPN to entry's VPN at N+1.** -/
theorem tlbVPNReg_set_after_fill {dom : DomainConfig}
    (doFillN : Signal dom Bool)
    (fillVPN tlb_vpn : Signal dom (BitVec 20)) (t : Nat)
    (h_fill : doFillN.val t = true) :
    (tlbVPNRegSignal doFillN fillVPN tlb_vpn).val (t + 1) = fillVPN.val t := by
  unfold tlbVPNRegSignal
  show (Signal.register 0#20 _).val (t + 1) = _
  show (tlbVPNNextSignal doFillN fillVPN tlb_vpn).val t = _
  unfold tlbVPNNextSignal Signal.mux
  show (if doFillN.val t = true then fillVPN.val t else tlb_vpn.val t) = fillVPN.val t
  rw [h_fill]
  rfl

/-! ## Combined: TLB fill at N → tlbHit on same VPN at N+1

  This is the "fill-then-hit" guarantee — the cornerstone of the
  multi-cycle invariant C reasoning. Combines the two register
  propagation lemmas (`tlbValidReg_set_after_fill`,
  `tlbVPNReg_set_after_fill`) with the per-entry hit predicate
  `tlbHitPure` (proven in MMU/TLB.lean as `tlbHit_valid_match`).

  Statement: when `doFillN.val t = true` (no SFENCE), the entry's
  hit-predicate evaluated on `fillVPN.val t` at cycle t+1 returns
  `true`, regardless of mega state (because in the non-mega case,
  entryVPN at t+1 = fillVPN at t, so `entryVPN == dVPN`; in the
  mega case, the high 10 bits also match by construction).
-/

/-- **Combined fill-then-hit (4kB-page case).**

    Stronger statement: if the fill happened at cycle t with mega=false,
    then at cycle t+1, `tlbHitPure` on the entry's stored VPN
    against `fillVPN.val t` returns true. -/
theorem tlbHit_after_fill_4k {dom : DomainConfig}
    (sfenceVMA doFillN tlb_valid : Signal dom Bool)
    (fillVPN tlb_vpn : Signal dom (BitVec 20)) (t : Nat)
    (h_no_sfence : sfenceVMA.val t = false)
    (h_fill : doFillN.val t = true) :
    tlbHitPure
      ((tlbValidRegSignal sfenceVMA doFillN tlb_valid).val (t + 1))
      false
      ((tlbVPNRegSignal doFillN fillVPN tlb_vpn).val (t + 1))
      (fillVPN.val t) = true := by
  rw [tlbValidReg_set_after_fill sfenceVMA doFillN tlb_valid t h_no_sfence h_fill]
  rw [tlbVPNReg_set_after_fill doFillN fillVPN tlb_vpn t h_fill]
  -- Goal: tlbHitPure true false (fillVPN.val t) (fillVPN.val t) = true
  unfold tlbHitPure tlbVPNMatchPure
  -- tlbVPNMatchPure false (fillVPN.val t) (fillVPN.val t) = (fillVPN.val t == fillVPN.val t)
  show (true && (if false = true then _
                 else (fillVPN.val t == fillVPN.val t))) = true
  simp

/-! ## Bridge to anyTLBHit

  The 4-way TLB has `anyTLBHitPure h0 h1 h2 h3 = (h0 || h1) ||
  (h2 || h3)` (proven in MMU/TLB.lean as `anyTLBHitPure_spec`).
  When any one entry hits, anyTLBHit fires (`anyTLBHit_h0..h3`
  in TLB.lean).

  So if `doFill0 t = true` (fill at entry 0 this cycle), and the
  N+1 lookup uses `dVPN = fillVPN.val t`, then the entry-0 hit
  fires by `tlbHit_after_fill_4k`, and `anyTLBHitPure` fires by
  `anyTLBHit_h0`.

  This connects the per-entry fill guarantee to the system-wide
  "any-hit" predicate that drives `useTranslatedAddr`. -/

/-- **Fill on entry 0 → anyTLBHit at N+1 for the same VPN (4kB).** -/
theorem anyTLBHit_after_fill0_4k {dom : DomainConfig}
    (sfenceVMA doFill0 tlb0_valid : Signal dom Bool)
    (fillVPN tlb0_vpn : Signal dom (BitVec 20)) (t : Nat)
    (hit1 hit2 hit3 : Bool)
    (h_no_sfence : sfenceVMA.val t = false)
    (h_fill : doFill0.val t = true) :
    anyTLBHitPure
      (tlbHitPure
        ((tlbValidRegSignal sfenceVMA doFill0 tlb0_valid).val (t + 1))
        false
        ((tlbVPNRegSignal doFill0 fillVPN tlb0_vpn).val (t + 1))
        (fillVPN.val t))
      hit1 hit2 hit3 = true := by
  rw [tlbHit_after_fill_4k sfenceVMA doFill0 tlb0_valid fillVPN tlb0_vpn t
        h_no_sfence h_fill]
  exact anyTLBHit_h0 hit1 hit2 hit3

end Sparkle.IP.RV32.MMU
