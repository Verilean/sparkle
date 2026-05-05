/-
  RV32 sstatus alias — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 949..950 read side, lines
  1418..1421 write side). Per RISC-V priv spec Vol II §4.1.1:

      sstatus is a "restricted view" of mstatus, exposing only the
      S-mode-relevant bits: SIE (1), SPIE (5), SPP (8), SUM (18),
      MXR (19). Other mstatus bits are read as 0 from sstatus and
      ignored on writes.

  In Sparkle the mask is `0x000C0122`:

      bit  1: SIE
      bit  5: SPIE
      bit  8: SPP
      bit 18: SUM
      bit 19: MXR

  Read view:
      sstatusView = mstatusReg ∧ sstatusMask

  Write merge: when the kernel writes sstatus via csrr*,
      sstatusWdataOut = (mstatusReg ∧ ¬sstatusMask)   -- preserve M-bits
                      ∨ (sstatusNewVal ∧ sstatusMask) -- update S-bits

  This file proves:
    1. sstatusView's bits outside the mask are 0.
    2. sstatusView's mask bits equal the corresponding mstatus bits.
    3. Write-merge preserves non-mask bits.
    4. Write-merge updates mask bits to the new value's mask bits.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure sstatus alias -/

/-- sstatus mask: bits {SIE=1, SPIE=5, SPP=8, SUM=18, MXR=19}. -/
@[inline] def sstatusMaskValuePure : BitVec 32 := 0x000C0122#32

/-- Read view: sstatus = mstatus ∧ sstatusMask. -/
@[inline] def sstatusViewPure (mstatus : BitVec 32) : BitVec 32 :=
  mstatus &&& sstatusMaskValuePure

/-- Write merge: combine the new sstatus value (mask bits) with the old
    mstatus (non-mask bits). -/
@[inline] def sstatusMergePure
    (mstatus sstatusNewVal : BitVec 32) : BitVec 32 :=
  (mstatus &&& (~~~sstatusMaskValuePure)) ||| (sstatusNewVal &&& sstatusMaskValuePure)

/-! ## Spec invariants — closed by `bv_decide` -/

/-- sstatus view's mask bits equal the corresponding mstatus bits. -/
theorem sstatusView_mask_bits (mstatus : BitVec 32) :
    sstatusViewPure mstatus &&& sstatusMaskValuePure
      = mstatus &&& sstatusMaskValuePure := by
  unfold sstatusViewPure
  bv_decide

/-- sstatus view's non-mask bits are 0. -/
theorem sstatusView_non_mask_zero (mstatus : BitVec 32) :
    sstatusViewPure mstatus &&& (~~~sstatusMaskValuePure) = 0#32 := by
  unfold sstatusViewPure
  bv_decide

/-- sstatus exposes SIE (bit 1) of mstatus. -/
theorem sstatusView_SIE (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 1 1 = mstatus.extractLsb' 1 1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus exposes SPIE (bit 5) of mstatus. -/
theorem sstatusView_SPIE (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 5 1 = mstatus.extractLsb' 5 1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus exposes SPP (bit 8) of mstatus. -/
theorem sstatusView_SPP (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 8 1 = mstatus.extractLsb' 8 1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus exposes SUM (bit 18) of mstatus. -/
theorem sstatusView_SUM (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 18 1 = mstatus.extractLsb' 18 1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus exposes MXR (bit 19) of mstatus. -/
theorem sstatusView_MXR (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 19 1 = mstatus.extractLsb' 19 1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus hides MIE (bit 3) — always 0 in sstatus. -/
theorem sstatusView_MIE_hidden (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 3 1 = 0#1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus hides MPIE (bit 7) — always 0 in sstatus. -/
theorem sstatusView_MPIE_hidden (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 7 1 = 0#1 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-- sstatus hides MPP (bits 11..12) — always 0 in sstatus. -/
theorem sstatusView_MPP_hidden (mstatus : BitVec 32) :
    (sstatusViewPure mstatus).extractLsb' 11 2 = 0#2 := by
  unfold sstatusViewPure sstatusMaskValuePure
  bv_decide

/-! ### Write-merge spec -/

/-- Write-merge preserves all non-mask bits of mstatus. -/
theorem sstatusMerge_preserves_non_mask
    (mstatus sstatusNewVal : BitVec 32) :
    sstatusMergePure mstatus sstatusNewVal &&& (~~~sstatusMaskValuePure)
      = mstatus &&& (~~~sstatusMaskValuePure) := by
  unfold sstatusMergePure
  bv_decide

/-- Write-merge updates mask bits to the corresponding bits of `sstatusNewVal`. -/
theorem sstatusMerge_updates_mask
    (mstatus sstatusNewVal : BitVec 32) :
    sstatusMergePure mstatus sstatusNewVal &&& sstatusMaskValuePure
      = sstatusNewVal &&& sstatusMaskValuePure := by
  unfold sstatusMergePure
  bv_decide

/-- Idempotency: write-merge of mstatus with its own sstatus view yields mstatus. -/
theorem sstatusMerge_idempotent_view (mstatus : BitVec 32) :
    sstatusMergePure mstatus (sstatusViewPure mstatus) = mstatus := by
  unfold sstatusMergePure sstatusViewPure
  bv_decide

/-! ## Composite spec -/

theorem sstatusViewPure_spec (mstatus : BitVec 32) :
    sstatusViewPure mstatus = mstatus &&& sstatusMaskValuePure := by
  rfl

theorem sstatusMergePure_spec (mstatus sstatusNewVal : BitVec 32) :
    sstatusMergePure mstatus sstatusNewVal =
      (mstatus &&& (~~~sstatusMaskValuePure))
        ||| (sstatusNewVal &&& sstatusMaskValuePure) := by
  rfl

/-! ## Signal-level wrappers -/

def sstatusViewSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mask : Signal dom (BitVec 32) := Signal.pure sstatusMaskValuePure
  mstatus &&& mask

def sstatusMergeSignal {dom : DomainConfig}
    (mstatus sstatusNewVal : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mask : Signal dom (BitVec 32) := Signal.pure sstatusMaskValuePure
  (mstatus &&& (~~~mask)) ||| (sstatusNewVal &&& mask)

end Sparkle.IP.RV32.CSR
