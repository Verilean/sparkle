/-
  RV32 mipSoftReg next-state — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1510..1518). The
  `mipSoftReg` shadow register stores the software-writable bits of
  `mip` (the {SSIP=1, STIP=5, SEIP=9} S-mode pending bits). When
  the kernel writes mip/sip via csrrw/csrrs/csrrc, only those three
  bits in `mipSoftReg` should update; bits outside the mask must
  be preserved.

  Spec (see also `CSR/MIP.lean` for the read side):

      mask = 0x00000222   -- bits {1, 5, 9}

      kept = mipSoft & ~mask   -- preserves non-S-bit lanes
      new  = (newCSR & mask) | kept

      mipSoftNext =
        if mipWriteEn then (kept | (mipNew & mask))
        else if sipWriteEn then (kept | (sipNew & mask))
        else mipSoft

  Invariants proven:
    * Bits outside the mask are preserved across any write.
    * S-bits get the new value when write fires.
    * mip-write takes priority over sip-write (matches SoC.lean).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure mipSoft next-state -/

/-- The software-writable bit mask: {SSIP=1, STIP=5, SEIP=9} = 0x222. -/
@[inline] def mipSoftMaskValuePure : BitVec 32 := 0x00000222#32

/-- mipSoftReg next-state: priority `mipWrite` > `sipWrite` > hold,
    with masked update preserving non-{SSIP,STIP,SEIP} bits. -/
@[inline] def mipSoftNextPure
    (mipWriteEn sipWriteEn : Bool)
    (mipNew sipNew mipSoft : BitVec 32) : BitVec 32 :=
  let mask  := mipSoftMaskValuePure
  let kept  := mipSoft &&& (~~~mask)
  if mipWriteEn then kept ||| (mipNew &&& mask)
  else if sipWriteEn then kept ||| (sipNew &&& mask)
  else mipSoft

/-! ## Spec invariants — closed by `bv_decide` -/

/-- No write fires → hold. -/
@[simp] theorem mipSoftNext_hold (mipNew sipNew mipSoft : BitVec 32) :
    mipSoftNextPure false false mipNew sipNew mipSoft = mipSoft := by
  rfl

/-- mip-write takes priority over sip-write. -/
@[simp] theorem mipSoftNext_mip_priority
    (sipWriteEn : Bool) (mipNew sipNew mipSoft : BitVec 32) :
    mipSoftNextPure true sipWriteEn mipNew sipNew mipSoft =
      (mipSoft &&& (~~~mipSoftMaskValuePure)) ||| (mipNew &&& mipSoftMaskValuePure) := by
  rfl

/-- sip-write applies when no mip-write. -/
@[simp] theorem mipSoftNext_sip_only
    (mipNew sipNew mipSoft : BitVec 32) :
    mipSoftNextPure false true mipNew sipNew mipSoft =
      (mipSoft &&& (~~~mipSoftMaskValuePure)) ||| (sipNew &&& mipSoftMaskValuePure) := by
  rfl

/-- **Bits outside the mask are preserved across any mip-write.** -/
theorem mipSoftNext_mip_preserves_non_mask
    (sipWriteEn : Bool) (mipNew sipNew mipSoft : BitVec 32) :
    (mipSoftNextPure true sipWriteEn mipNew sipNew mipSoft) &&& (~~~mipSoftMaskValuePure)
      = mipSoft &&& (~~~mipSoftMaskValuePure) := by
  unfold mipSoftNextPure
  bv_decide

/-- **Bits outside the mask are preserved across any sip-write.** -/
theorem mipSoftNext_sip_preserves_non_mask
    (mipNew sipNew mipSoft : BitVec 32) :
    (mipSoftNextPure false true mipNew sipNew mipSoft) &&& (~~~mipSoftMaskValuePure)
      = mipSoft &&& (~~~mipSoftMaskValuePure) := by
  unfold mipSoftNextPure
  bv_decide

/-- **S-bits update to the new mip value when mip-write fires.** -/
theorem mipSoftNext_mip_updates_S_bits
    (sipWriteEn : Bool) (mipNew sipNew mipSoft : BitVec 32) :
    (mipSoftNextPure true sipWriteEn mipNew sipNew mipSoft) &&& mipSoftMaskValuePure
      = mipNew &&& mipSoftMaskValuePure := by
  unfold mipSoftNextPure
  bv_decide

/-- **S-bits update to the new sip value when sip-write fires (no mip-write).** -/
theorem mipSoftNext_sip_updates_S_bits
    (mipNew sipNew mipSoft : BitVec 32) :
    (mipSoftNextPure false true mipNew sipNew mipSoft) &&& mipSoftMaskValuePure
      = sipNew &&& mipSoftMaskValuePure := by
  unfold mipSoftNextPure
  bv_decide

/-- The mask `0x222` selects exactly bits {1, 5, 9}: SSIP, STIP, SEIP.
    `0x222 = 0010 0010 0010` in binary. -/
theorem mipSoftMaskValue_bits :
    mipSoftMaskValuePure.extractLsb' 1 1 = 1#1 ∧
    mipSoftMaskValuePure.extractLsb' 5 1 = 1#1 ∧
    mipSoftMaskValuePure.extractLsb' 9 1 = 1#1 ∧
    mipSoftMaskValuePure.extractLsb' 0 1 = 0#1 ∧
    mipSoftMaskValuePure.extractLsb' 2 1 = 0#1 := by
  unfold mipSoftMaskValuePure
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-! ## Composite spec -/

theorem mipSoftNextPure_spec :
    ∀ (mipWriteEn sipWriteEn : Bool)
      (mipNew sipNew mipSoft : BitVec 32),
      mipSoftNextPure mipWriteEn sipWriteEn mipNew sipNew mipSoft =
        (let mask := mipSoftMaskValuePure
         let kept := mipSoft &&& (~~~mask)
         if mipWriteEn then kept ||| (mipNew &&& mask)
         else if sipWriteEn then kept ||| (sipNew &&& mask)
         else mipSoft) := by
  intros; rfl

/-! ## Signal-level wrapper -/

def mipSoftNextSignal {dom : DomainConfig}
    (mipWriteEn sipWriteEn : Signal dom Bool)
    (mipNew sipNew mipSoft : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mask : Signal dom (BitVec 32) := Signal.pure mipSoftMaskValuePure
  let kept := mipSoft &&& (~~~mask)
  let mipMaskedNew := mipNew &&& mask
  let sipMaskedNew := sipNew &&& mask
  Signal.mux mipWriteEn (kept ||| mipMaskedNew)
    (Signal.mux sipWriteEn (kept ||| sipMaskedNew) mipSoft)

end Sparkle.IP.RV32.CSR
