/-
  RV32 Sv32 PTE flag decoding — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1640..1645). A Sv32
  page-table entry (PTE) is a 32-bit value with the following
  layout (per RISC-V priv §4.3.1, Table 4.18):

    bit  31..20  PPN[1]    (12 bits, megapage frame number)
    bit  19..10  PPN[0]    (10 bits, regular frame number)
    bit  9..8    RSW       reserved for software use
    bit  7       D         dirty
    bit  6       A         accessed
    bit  5       G         global
    bit  4       U         user-accessible
    bit  3       X         executable (leaf if set)
    bit  2       W         writable
    bit  1       R         readable (leaf if set)
    bit  0       V         valid

  The "leaf" bit is `R ∨ X`: a PTE is a leaf iff it grants either
  read or execute permission. Otherwise it's a pointer to the
  next page-table level.

  This file proves the per-bit decoders + the leaf invariant.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure PTE flag decoders -/

/-- PTE.V (valid bit): bit 0. -/
@[inline] def pteValidPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 0 1 == 1#1

/-- PTE.R (readable bit): bit 1. -/
@[inline] def pteRBitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 1 1 == 1#1

/-- PTE.W (writable bit): bit 2. -/
@[inline] def pteWBitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 2 1 == 1#1

/-- PTE.X (executable bit): bit 3. -/
@[inline] def pteXBitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 3 1 == 1#1

/-- PTE.U (user-accessible bit): bit 4. -/
@[inline] def pteUBitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 4 1 == 1#1

/-- PTE.G (global bit): bit 5. -/
@[inline] def pteGBitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 5 1 == 1#1

/-- PTE.A (accessed bit): bit 6. -/
@[inline] def pteABitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 6 1 == 1#1

/-- PTE.D (dirty bit): bit 7. -/
@[inline] def pteDBitPure (pte : BitVec 32) : Bool :=
  pte.extractLsb' 7 1 == 1#1

/-- PTE is a "leaf": R ∨ X. -/
@[inline] def pteIsLeafPure (pte : BitVec 32) : Bool :=
  pteRBitPure pte || pteXBitPure pte

/-- PTE is invalid: V = 0. -/
@[inline] def pteInvalidPure (pte : BitVec 32) : Bool :=
  !pteValidPure pte

/-- Low 8 bits of PTE: the flags field {V,R,W,X,U,G,A,D}. -/
@[inline] def pteFlagsPure (pte : BitVec 32) : BitVec 8 :=
  pte.extractLsb' 0 8

/-! ## Spec invariants — closed by `bv_decide` -/

/-- pteValid is the V bit. -/
theorem pteValid_bit (pte : BitVec 32) :
    pteValidPure pte = (pte.extractLsb' 0 1 == 1#1) := by rfl

/-- pteIsLeaf is R || X. -/
theorem pteIsLeaf_bits (pte : BitVec 32) :
    pteIsLeafPure pte =
      ((pte.extractLsb' 1 1 == 1#1) || (pte.extractLsb' 3 1 == 1#1)) := by
  rfl

/-- pteInvalid is the negation of pteValid. -/
theorem pteInvalid_neg_valid (pte : BitVec 32) :
    pteInvalidPure pte = !pteValidPure pte := by rfl

/-- A PTE with V=1, R=1 is a leaf. -/
theorem pteLeaf_when_R (pte : BitVec 32)
    (h : pte.extractLsb' 1 1 = 1#1) :
    pteIsLeafPure pte = true := by
  unfold pteIsLeafPure pteRBitPure
  rw [h]
  rfl

/-- A PTE with V=1, X=1 is a leaf. -/
theorem pteLeaf_when_X (pte : BitVec 32)
    (h : pte.extractLsb' 3 1 = 1#1) :
    pteIsLeafPure pte = true := by
  unfold pteIsLeafPure pteRBitPure pteXBitPure
  rw [h]
  cases pte.extractLsb' 1 1 == 1#1 <;> rfl

/-- A PTE with R=0, X=0 is NOT a leaf (pointer to next level). -/
theorem pteNotLeaf_when_no_RX (pte : BitVec 32)
    (hR : pte.extractLsb' 1 1 = 0#1)
    (hX : pte.extractLsb' 3 1 = 0#1) :
    pteIsLeafPure pte = false := by
  unfold pteIsLeafPure pteRBitPure pteXBitPure
  rw [hR, hX]
  rfl

/-- pteFlags low byte: bit 0 is V. -/
theorem pteFlags_V (pte : BitVec 32) :
    (pteFlagsPure pte).extractLsb' 0 1 = pte.extractLsb' 0 1 := by
  unfold pteFlagsPure
  bv_decide

/-- pteFlags low byte: bit 1 is R. -/
theorem pteFlags_R (pte : BitVec 32) :
    (pteFlagsPure pte).extractLsb' 1 1 = pte.extractLsb' 1 1 := by
  unfold pteFlagsPure
  bv_decide

/-- pteFlags low byte: bit 3 is X. -/
theorem pteFlags_X (pte : BitVec 32) :
    (pteFlagsPure pte).extractLsb' 3 1 = pte.extractLsb' 3 1 := by
  unfold pteFlagsPure
  bv_decide

/-- An invalid PTE has bit 0 = 0 (whole-bit form, bv_decide). -/
theorem pteInvalid_bit0_zero (pte : BitVec 32)
    (h : pteInvalidPure pte = true) :
    pte.extractLsb' 0 1 = 0#1 := by
  unfold pteInvalidPure pteValidPure at h
  have hne : (pte.extractLsb' 0 1 == 1#1) = false := by
    cases h_eq : pte.extractLsb' 0 1 == 1#1
    · rfl
    · simp [h_eq] at h
  -- BitVec 1 has two values: 0#1 and 1#1. !(== 1#1) ⇒ = 0#1.
  have : ¬ (pte.extractLsb' 0 1 = 1#1) := by
    intro heq
    rw [heq] at hne
    simp at hne
  -- Use bv_decide to close — given the inequality, the value must be 0#1.
  revert this
  generalize pte.extractLsb' 0 1 = b
  intro h2
  bv_decide

/-! ## Composite specs -/

theorem pteValidPure_spec (pte : BitVec 32) :
    pteValidPure pte = (pte.extractLsb' 0 1 == 1#1) := by rfl

theorem pteIsLeafPure_spec (pte : BitVec 32) :
    pteIsLeafPure pte = (pteRBitPure pte || pteXBitPure pte) := by rfl

/-! ## Signal-level wrappers -/

def pteValidSignal {dom : DomainConfig}
    (pte : Signal dom (BitVec 32)) : Signal dom Bool :=
  (pte.map (BitVec.extractLsb' 0 1 ·)) === 1#1

def pteRBitSignal {dom : DomainConfig}
    (pte : Signal dom (BitVec 32)) : Signal dom Bool :=
  (pte.map (BitVec.extractLsb' 1 1 ·)) === 1#1

def pteXBitSignal {dom : DomainConfig}
    (pte : Signal dom (BitVec 32)) : Signal dom Bool :=
  (pte.map (BitVec.extractLsb' 3 1 ·)) === 1#1

def pteIsLeafSignal {dom : DomainConfig}
    (pte : Signal dom (BitVec 32)) : Signal dom Bool :=
  pteRBitSignal pte ||| pteXBitSignal pte

def pteInvalidSignal {dom : DomainConfig}
    (pte : Signal dom (BitVec 32)) : Signal dom Bool :=
  ~~~(pteValidSignal pte)

def pteFlagsSignal {dom : DomainConfig}
    (pte : Signal dom (BitVec 32)) : Signal dom (BitVec 8) :=
  pte.map (BitVec.extractLsb' 0 8 ·)

end Sparkle.IP.RV32.MMU
