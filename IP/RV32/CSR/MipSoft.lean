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

/-! ## sip read value

  When the kernel reads `sip`, it sees only the soft-writable
  bits (SSIP, STIP, SEIP) of mip — the hardware-only bits
  (MTIP, MSIP, MEIP) are masked out. This is `mipValue ∧
  mipSoftMaskValue` per RISC-V priv spec, Vol II §4.1.5.
-/

@[inline] def sipReadValuePure (mipValue : BitVec 32) : BitVec 32 :=
  mipValue &&& mipSoftMaskValuePure

/-- sip-read masks out the high 20 bits (none are soft-writable). -/
theorem sipReadValue_high_zero (mipValue : BitVec 32) :
    (sipReadValuePure mipValue).extractLsb' 12 20 = 0#20 := by
  unfold sipReadValuePure mipSoftMaskValuePure
  bv_decide

/-- sip-read on a pure-MSIP value masks it out (MSIP is not soft-writable). -/
theorem sipReadValue_msip_masked :
    sipReadValuePure 0x00000008#32 = 0#32 := by
  unfold sipReadValuePure mipSoftMaskValuePure
  bv_decide

theorem sipReadValuePure_spec (mipValue : BitVec 32) :
    sipReadValuePure mipValue = (mipValue &&& mipSoftMaskValuePure) := rfl

def sipReadValueSignal {dom : DomainConfig}
    (mipValue : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mask : Signal dom (BitVec 32) := Signal.pure mipSoftMaskValuePure
  mipValue &&& mask

/-! ## Sequential mipSoftReg: hold when both WEs are false

  `mipSoftReg` is a `Signal.register 0#32 (mipSoftNextSignal ...)`.
  When both `mipWriteEn` and `sipWriteEn` are false at cycle t,
  the register at cycle t+1 holds its old value `mipSoft.val t`.

  Combined with `trap_clears_idex_isCsr_valid` (Pipeline/SuppressEXWB),
  a trap at cycle t implies both `mipWriteEn` (= csrRegWeSignal
  idex_isCsr_valid csrIsMip) and `sipWriteEn` (csrRegWeSignal
  idex_isCsr_valid csrIsSip) are false at cycle t — so mipSoftReg
  is held across trap entry.
-/

/-- mipSoftReg signal wrapper. -/
def mipSoftRegSignal {dom : DomainConfig}
    (init : BitVec 32) (mipWriteEn sipWriteEn : Signal dom Bool)
    (mipNew sipNew mipSoft : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.register init
    (mipSoftNextSignal mipWriteEn sipWriteEn mipNew sipNew mipSoft)

/-- **Both WEs false at t → mipSoftReg at t+1 = mipSoft.val t.**

    Direct proof by unfolding the Signal.register and the nested
    Signal.muxes. -/
theorem mipSoftReg_hold_when_no_we {dom : DomainConfig}
    (init : BitVec 32) (mipWriteEn sipWriteEn : Signal dom Bool)
    (mipNew sipNew mipSoft : Signal dom (BitVec 32)) (t : Nat)
    (h_no_mw : mipWriteEn.val t = false)
    (h_no_sw : sipWriteEn.val t = false) :
    (mipSoftRegSignal init mipWriteEn sipWriteEn mipNew sipNew mipSoft).val (t + 1) =
      mipSoft.val t := by
  unfold mipSoftRegSignal mipSoftNextSignal
  show (Signal.register init _).val (t + 1) = _
  -- (register init next).val (t+1) = next.val t. The next signal is a
  -- nested Signal.mux on mipWriteEn then sipWriteEn; both are false at t,
  -- so it reduces to mipSoft.val t.
  unfold Signal.mux
  -- After unfold, the .val t becomes a nested if-then-else.
  show (if mipWriteEn.val t then _ else
    (if sipWriteEn.val t then _ else mipSoft.val t)) = mipSoft.val t
  rw [h_no_mw, h_no_sw]
  rfl

/-! ## Cycle-N+2 mipSoftReg stability across trap

  When neither WE fires at cycle N+1 (e.g., post-IDEX-squash),
  mipSoftReg at N+2 = mipSoft at N+1. This is the cycle-N+2
  hold form: callers can chain it with the cycle-N+1 hold to
  show 2-cycle stability when both cycles have no WE event.
-/

/-- **No-WE at N+1 → mipSoftReg at N+2 = mipSoft at N+1.**

    Same shape as `mipSoftReg_hold_when_no_we` but indexed at
    cycle N+1 instead of N. Provided as a named lemma for
    composite-proof readability. -/
theorem mipSoftReg_hold_when_no_we_at_N_plus_1 {dom : DomainConfig}
    (init : BitVec 32) (mipWriteEn sipWriteEn : Signal dom Bool)
    (mipNew sipNew mipSoft : Signal dom (BitVec 32)) (n : Nat)
    (h_no_mw_n1 : mipWriteEn.val (n + 1) = false)
    (h_no_sw_n1 : sipWriteEn.val (n + 1) = false) :
    (mipSoftRegSignal init mipWriteEn sipWriteEn mipNew sipNew mipSoft).val (n + 2) =
      mipSoft.val (n + 1) :=
  mipSoftReg_hold_when_no_we init mipWriteEn sipWriteEn mipNew sipNew mipSoft
    (n + 1) h_no_mw_n1 h_no_sw_n1

/-! ## LTL form -/

/-- **LTL form of `mipSoftReg_hold_when_no_we`.** -/
theorem mipSoftReg_hold_when_no_we_LTL {dom : DomainConfig}
    (init : BitVec 32) (mipWriteEn sipWriteEn : Signal dom Bool)
    (mipNew sipNew mipSoft : Signal dom (BitVec 32)) :
    ∀ t, mipWriteEn.val t = false → sipWriteEn.val t = false →
         (mipSoftRegSignal init mipWriteEn sipWriteEn mipNew sipNew mipSoft).val (t + 1) =
           mipSoft.val t :=
  fun t => mipSoftReg_hold_when_no_we init mipWriteEn sipWriteEn mipNew sipNew mipSoft t
