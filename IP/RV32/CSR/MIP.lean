/-
  RV32 mip / sip value construction — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 898..903). Computes the
  `mip` CSR's read-time value by combining:

    * Hardware bits: MTIP (bit 7) from `timerIrq`,
                     MSIP (bit 3) from `swIrq`.
    * Software bits: SSIP (bit 1), STIP (bit 5), SEIP (bit 9) from
                     `mipSoftReg`, masked to those three positions.

  Spec (per RISC-V priv spec §3.1.6 mip):

    mipValue = (timerIrq ? 0x80 : 0)
             | (swIrq    ? 0x08 : 0)
             | (mipSoftReg & 0x222)

  The mask `0x222` selects bits {1 (SSIP), 5 (STIP), 9 (SEIP)} —
  the S-mode pending-interrupt bits that are software-writable.
  All other software-writable bits in mip are 0 in this SoC
  (no external M-mode interrupt, no platform-defined bits).

  This file proves the per-bit invariants — which mip bits are
  set/clear given a particular mipSoftReg, timerIrq, swIrq.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure mipValue -/

/-- mip's read-time value. -/
@[inline] def mipValuePure
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) : BitVec 32 :=
  let mipTimerBit : BitVec 32 := if timerIrq then 0x00000080#32 else 0#32
  let mipSwBit    : BitVec 32 := if swIrq    then 0x00000008#32 else 0#32
  let mipSoftMask : BitVec 32 := 0x00000222#32
  mipTimerBit ||| mipSwBit ||| (mipSoftReg &&& mipSoftMask)

/-! ## Per-bit invariants — closed by `bv_decide` -/

/-- MTIP (bit 7) reflects `timerIrq`. -/
theorem mip_MTIP_eq_timerIrq
    (swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure true swIrq mipSoftReg).extractLsb' 7 1 = 1#1 := by
  unfold mipValuePure
  bv_decide

theorem mip_MTIP_clear_when_no_irq
    (swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure false swIrq mipSoftReg).extractLsb' 7 1 = 0#1 := by
  unfold mipValuePure
  -- mipSoftReg & 0x222 has bit 7 = 0 (mask is 0x222 → bit 7 clear)
  bv_decide

/-- MSIP (bit 3) reflects `swIrq`. -/
theorem mip_MSIP_eq_swIrq
    (timerIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq true mipSoftReg).extractLsb' 3 1 = 1#1 := by
  unfold mipValuePure
  bv_decide

theorem mip_MSIP_clear_when_no_irq
    (timerIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq false mipSoftReg).extractLsb' 3 1 = 0#1 := by
  unfold mipValuePure
  bv_decide

/-- SSIP (bit 1) is exactly mipSoftReg[1]. -/
theorem mip_SSIP_eq_softReg
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq swIrq mipSoftReg).extractLsb' 1 1
      = mipSoftReg.extractLsb' 1 1 := by
  unfold mipValuePure
  bv_decide

/-- STIP (bit 5) is exactly mipSoftReg[5]. -/
theorem mip_STIP_eq_softReg
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq swIrq mipSoftReg).extractLsb' 5 1
      = mipSoftReg.extractLsb' 5 1 := by
  unfold mipValuePure
  bv_decide

/-- SEIP (bit 9) is exactly mipSoftReg[9]. -/
theorem mip_SEIP_eq_softReg
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq swIrq mipSoftReg).extractLsb' 9 1
      = mipSoftReg.extractLsb' 9 1 := by
  unfold mipValuePure
  bv_decide

/-- Bit 0 (reserved) is always 0. -/
theorem mip_bit0_zero
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq swIrq mipSoftReg).extractLsb' 0 1 = 0#1 := by
  unfold mipValuePure
  bv_decide

/-- Bit 2 (reserved) is always 0. -/
theorem mip_bit2_zero
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    (mipValuePure timerIrq swIrq mipSoftReg).extractLsb' 2 1 = 0#1 := by
  unfold mipValuePure
  bv_decide

/-- The high half (bits 31..10 except bit 9) is always 0. Encoded as:
    masking the result with all-bits-clear-except-{1,3,5,7,9} yields
    the same value (i.e. no other bits are set). -/
theorem mip_only_known_bits
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    mipValuePure timerIrq swIrq mipSoftReg
      &&& (~~~ 0x000002AA#32) = 0#32 := by
  unfold mipValuePure
  bv_decide

/-! ## Composite spec -/

/-- mip's value is fully determined by the three inputs. The mask is
    explicit. -/
theorem mipValuePure_spec
    (timerIrq swIrq : Bool) (mipSoftReg : BitVec 32) :
    mipValuePure timerIrq swIrq mipSoftReg =
      ((if timerIrq then 0x00000080#32 else 0#32)
       ||| (if swIrq then 0x00000008#32 else 0#32)
       ||| (mipSoftReg &&& 0x00000222#32)) := by
  rfl

/-! ## Signal-level wrapper -/

def mipValueSignal {dom : DomainConfig}
    (timerIrq swIrq : Signal dom Bool)
    (mipSoftReg : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mipTimerBit := Signal.mux timerIrq (Signal.pure 0x00000080#32) (Signal.pure 0#32)
  let mipSwBit    := Signal.mux swIrq (Signal.pure 0x00000008#32) (Signal.pure 0#32)
  let mipSoftMask : Signal dom (BitVec 32) := Signal.pure 0x00000222#32
  mipTimerBit ||| mipSwBit ||| (mipSoftReg &&& mipSoftMask)

/-- The mask exposed as a top-level definition so call sites can share it. -/
def mipSoftMaskValue : BitVec 32 := 0x00000222#32

end Sparkle.IP.RV32.CSR
