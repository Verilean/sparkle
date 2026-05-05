/-
  RV32 mstatus bit-field accessors — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1085..1087). The
  mstatus CSR (priv §3.1.6) packs many fields into a 32-bit
  word. This file factors out the bit-field accessors used in
  trap entry / sret / mret transitions:

    bit  1     SIE
    bit  3     MIE
    bit  5     SPIE
    bit  7     MPIE
    bit  8     SPP   (privilege at S-trap entry: 0=U, 1=S)
    bit 11..12 MPP   (privilege at M-trap entry: 0=U, 1=S, 3=M)
    bit 17     SUM   (sstatus alias)
    bit 18     MXR   (sstatus alias)

  This file extracts MPP/SPP and the `sretPriv` derivation:

    sretPriv = 0 ## SPP  (BitVec 2 = 00 ‖ SPP_bit)
                       — privilege returned to on SRET
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure mstatus bit accessors -/

/-- MPP: mstatus[12:11] — 2-bit privilege at M-trap entry. -/
@[inline] def mppPure (mstatus : BitVec 32) : BitVec 2 :=
  mstatus.extractLsb' 11 2

/-- SPP: mstatus[8] — 1-bit privilege at S-trap entry. -/
@[inline] def sppBitPure (mstatus : BitVec 32) : BitVec 1 :=
  mstatus.extractLsb' 8 1

/-- sretPriv: privilege after SRET = 0 ‖ SPP. -/
@[inline] def sretPrivPure (mstatus : BitVec 32) : BitVec 2 :=
  (0#1 : BitVec 1) ++ sppBitPure mstatus

/-! ## Spec invariants — closed by `bv_decide` -/

/-- MPP is bits 12:11 of mstatus. -/
theorem mpp_bits (mstatus : BitVec 32) :
    mppPure mstatus = mstatus.extractLsb' 11 2 := by rfl

/-- SPP is bit 8 of mstatus. -/
theorem sppBit_bit (mstatus : BitVec 32) :
    sppBitPure mstatus = mstatus.extractLsb' 8 1 := by rfl

/-- sretPriv's high bit is always 0 (SPP can only encode U or S). -/
theorem sretPriv_high_zero (mstatus : BitVec 32) :
    (sretPrivPure mstatus).extractLsb' 1 1 = 0#1 := by
  unfold sretPrivPure
  bv_decide

/-- sretPriv's low bit equals SPP. -/
theorem sretPriv_low_eq_spp (mstatus : BitVec 32) :
    (sretPrivPure mstatus).extractLsb' 0 1 = sppBitPure mstatus := by
  unfold sretPrivPure sppBitPure
  bv_decide

/-- sretPriv encodes either U-mode (00) or S-mode (01) — never M. -/
theorem sretPriv_le_S (mstatus : BitVec 32) :
    (sretPrivPure mstatus = 0#2) ∨ (sretPrivPure mstatus = 1#2) := by
  unfold sretPrivPure sppBitPure
  -- The 0##bit BV either equals 0##0 (=0) or 0##1 (=1) per the bit
  -- range of extractLsb' 8 1 (just the SPP bit).
  -- bv_decide can't directly prove disjunctions; case-split on the bit.
  have hb : mstatus.extractLsb' 8 1 = 0#1 ∨ mstatus.extractLsb' 8 1 = 1#1 := by
    have h := mstatus.extractLsb' 8 1
    -- BitVec 1 has only two values
    bv_omega
  rcases hb with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

/-! ## Composite specs -/

theorem mppPure_spec (mstatus : BitVec 32) :
    mppPure mstatus = mstatus.extractLsb' 11 2 := by rfl

theorem sppBitPure_spec (mstatus : BitVec 32) :
    sppBitPure mstatus = mstatus.extractLsb' 8 1 := by rfl

theorem sretPrivPure_spec (mstatus : BitVec 32) :
    sretPrivPure mstatus = (0#1 : BitVec 1) ++ mstatus.extractLsb' 8 1 := by rfl

/-! ## Signal-level wrappers -/

def mppSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32)) : Signal dom (BitVec 2) :=
  mstatus.map (BitVec.extractLsb' 11 2 ·)

def sppBitSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32)) : Signal dom (BitVec 1) :=
  mstatus.map (BitVec.extractLsb' 8 1 ·)

def sretPrivSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32)) : Signal dom (BitVec 2) :=
  let zero1 : Signal dom (BitVec 1) := Signal.pure 0#1
  zero1 ++ sppBitSignal mstatus

end Sparkle.IP.RV32.CSR
