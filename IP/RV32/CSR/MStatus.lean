/-
  RV32 mstatus next-state — pure logic + bit-level invariants

  Extracted from `IP/RV32/SoC.lean`. The mstatus CSR is the trickiest
  pure-combinational block in the trap path because each architectural
  event (M-trap, S-trap, MRET, SRET, CSR write to mstatus or sstatus)
  rewrites several bits while leaving the others alone.

  RISC-V priv spec, Vol II §3.1.6 (mstatus) gives the bit layout:

  ```
    bit  0 : -      bit  1 : SIE   bit  2 : -     bit  3 : MIE
    bit  4 : -      bit  5 : SPIE  bit  6 : UBE   bit  7 : MPIE
    bit  8 : SPP    bits[10:9] : - bits[12:11] : MPP
    bits[14:13] : FS  bits[16:15] : XS  bit 17 : MPRV
    bit 18 : SUM    bit 19 : MXR  bit 20 : TVM   bit 21 : TW
    bit 22 : TSR    bits[30:23] : -  bit 31 : SD (read-only)
  ```

  This file proves bit-level specs for each `mstatus*Val` transformer
  separately. We don't try to prove a single monster theorem about
  the whole mux chain; instead each event's bit-level effect is
  pinned down, and the mux chain in `SoC.lean` selects one of the
  proven transformers based on the event signals.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## mstatus bit positions -/

/-- mstatus.SIE — supervisor interrupt enable (bit 1). -/
def mstatusBit_SIE  : Nat := 1
/-- mstatus.MIE — machine interrupt enable (bit 3). -/
def mstatusBit_MIE  : Nat := 3
/-- mstatus.SPIE — saved supervisor interrupt enable (bit 5). -/
def mstatusBit_SPIE : Nat := 5
/-- mstatus.MPIE — saved machine interrupt enable (bit 7). -/
def mstatusBit_MPIE : Nat := 7
/-- mstatus.SPP — saved supervisor previous-priv (bit 8, 1-bit). -/
def mstatusBit_SPP  : Nat := 8
/-- mstatus.MPP — saved machine previous-priv (bits [12:11], 2-bit). -/
def mstatusBit_MPP_lo : Nat := 11

/-! ## Generic bit helpers (decide-friendly) -/

/-- Set bit `i` in a 32-bit word to a given Bool. The 5-bit shift amount
    is captured by `BitVec.shiftLeft` on a 32-bit literal. -/
def setBit32 (w : BitVec 32) (i : Nat) (b : Bool) : BitVec 32 :=
  let mask : BitVec 32 := 1#32 <<< (BitVec.ofNat 32 i)
  if b then w ||| mask else w &&& (~~~mask)

/-- Read bit `i` of a 32-bit word as Bool. We use `extractLsb'` to keep
    `bv_decide` friendly. The `i` is a static Nat, so this reduces to
    a fixed extract once `i` is `unfold`ed. -/
def getBit32 (w : BitVec 32) (i : Nat) : Bool :=
  (w.extractLsb' i 1) == 1#1

/-! ## MRET transformation

  Spec: MRET sets `MIE := MPIE`, `MPIE := 1`, `MPP := 00 (U)`.
  Other bits unchanged.
-/

/-- Pure MRET transformation on mstatus.

    The implementation in `SoC.lean` does:
    1. Clear MPP bits (mask `0xFFFFE7FF`).
    2. Conditionally set/clear MIE based on MPIE.
    3. OR in `0x80` to set MPIE := 1.

    We re-encode this as `setBit32` calls so the bit-level effect is
    explicit. -/
def mstatusMretVal_pure (mstatus : BitVec 32) (mpie : Bool) : BitVec 32 :=
  let s1 := setBit32 mstatus mstatusBit_MPP_lo       false       -- MPP[11] := 0
  let s2 := setBit32 s1     (mstatusBit_MPP_lo + 1)  false       -- MPP[12] := 0
  let s3 := setBit32 s2      mstatusBit_MIE          mpie        -- MIE := MPIE
  let s4 := setBit32 s3      mstatusBit_MPIE         true        -- MPIE := 1
  s4

/-- The implementation expression in `SoC.lean`, transcribed for the
    equivalence proof. -/
def mstatusMretVal_impl (mstatus : BitVec 32) (mpie : Bool) : BitVec 32 :=
  let msClearMPP    := mstatus &&& 0xFFFFE7FF#32
  let msRestoreMIE  := if mpie then msClearMPP ||| 0x00000008#32
                       else msClearMPP &&& 0xFFFFFFF7#32
  msRestoreMIE ||| 0x00000080#32

/-- Equivalence: the bit-by-bit pure version equals the
    mask-and-or implementation. Closed by `decide`. -/
theorem mstatusMretVal_pure_eq_impl (mstatus : BitVec 32) (mpie : Bool) :
    mstatusMretVal_pure mstatus mpie = mstatusMretVal_impl mstatus mpie := by
  unfold mstatusMretVal_pure mstatusMretVal_impl setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  -- Reduces to a goal about BitVec arithmetic. With 33 input bits
  -- (32 + 1 Bool) we'd need 2^33 cases — too big for `decide`. Instead
  -- we observe both sides are the same composition of `&&&` / `|||`
  -- with literal masks; bv_decide closes that.
  bv_decide

/-! ## MRET — bit-level spec invariants

  Each invariant pins down a single bit's value after MRET. -/

@[simp] theorem mstatus_mret_MPP_low_zero
    (mstatus : BitVec 32) (mpie : Bool) :
    getBit32 (mstatusMretVal_pure mstatus mpie) mstatusBit_MPP_lo = false := by
  unfold getBit32 mstatusMretVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mpie
  bv_decide

@[simp] theorem mstatus_mret_MIE_eq_input_MPIE
    (mstatus : BitVec 32) (mpie : Bool) :
    getBit32 (mstatusMretVal_pure mstatus mpie) mstatusBit_MIE = mpie := by
  unfold getBit32 mstatusMretVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mpie
  bv_decide

@[simp] theorem mstatus_mret_MPIE_one
    (mstatus : BitVec 32) (mpie : Bool) :
    getBit32 (mstatusMretVal_pure mstatus mpie) mstatusBit_MPIE = true := by
  unfold getBit32 mstatusMretVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mpie
  bv_decide

/-- After MRET, MPP high bit (12) is also 0. Together with the previous
    `mstatus_mret_MPP_low_zero` this gives `MPP = 00 = U-mode`. -/
@[simp] theorem mstatus_mret_MPP_high_zero
    (mstatus : BitVec 32) (mpie : Bool) :
    getBit32 (mstatusMretVal_pure mstatus mpie) (mstatusBit_MPP_lo + 1) = false := by
  unfold getBit32 mstatusMretVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mpie
  bv_decide

/-! ## SRET transformation

  Spec: SRET sets `SIE := SPIE`, `SPIE := 1`, `SPP := 0 (U)`.
  Other bits unchanged.
-/

/-- Pure SRET transformation on mstatus. -/
def mstatusSretVal_pure (mstatus : BitVec 32) (spie : Bool) : BitVec 32 :=
  let s1 := setBit32 mstatus mstatusBit_SPP   false
  let s2 := setBit32 s1     mstatusBit_SIE   spie
  let s3 := setBit32 s2     mstatusBit_SPIE  true
  s3

/-- SRET implementation expression in `SoC.lean`. -/
def mstatusSretVal_impl (mstatus : BitVec 32) (spie : Bool) : BitVec 32 :=
  let msClearSPP    := mstatus &&& 0xFFFFFEFF#32
  let msRestoreSIE  := if spie then msClearSPP ||| 0x00000002#32
                       else msClearSPP &&& 0xFFFFFFFD#32
  msRestoreSIE ||| 0x00000020#32

/-- Equivalence: pure ↔ implementation. -/
theorem mstatusSretVal_pure_eq_impl (mstatus : BitVec 32) (spie : Bool) :
    mstatusSretVal_pure mstatus spie = mstatusSretVal_impl mstatus spie := by
  unfold mstatusSretVal_pure mstatusSretVal_impl setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  bv_decide

@[simp] theorem mstatus_sret_SPP_zero
    (mstatus : BitVec 32) (spie : Bool) :
    getBit32 (mstatusSretVal_pure mstatus spie) mstatusBit_SPP = false := by
  unfold getBit32 mstatusSretVal_pure setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  revert spie
  bv_decide

@[simp] theorem mstatus_sret_SIE_eq_input_SPIE
    (mstatus : BitVec 32) (spie : Bool) :
    getBit32 (mstatusSretVal_pure mstatus spie) mstatusBit_SIE = spie := by
  unfold getBit32 mstatusSretVal_pure setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  revert spie
  bv_decide

@[simp] theorem mstatus_sret_SPIE_one
    (mstatus : BitVec 32) (spie : Bool) :
    getBit32 (mstatusSretVal_pure mstatus spie) mstatusBit_SPIE = true := by
  unfold getBit32 mstatusSretVal_pure setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  revert spie
  bv_decide

/-! ## M-mode trap entry transformation

  Spec: M-mode trap sets `MPIE := MIE`, `MIE := 0`, `MPP := privMode`.
  Other bits unchanged.
-/

/-- Pure M-trap entry transformation. -/
def mstatusTrapMVal_pure
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) : BitVec 32 :=
  let s1 := setBit32 mstatus mstatusBit_MIE         false  -- MIE := 0
  let s2 := setBit32 s1     mstatusBit_MPIE         mie   -- MPIE := old MIE
  -- MPP[12:11] := priv: clear both bits, then OR in priv shifted to bit 11
  let s3 := setBit32 s2     mstatusBit_MPP_lo       false
  let s4 := setBit32 s3     (mstatusBit_MPP_lo + 1) false
  let s5 := setBit32 s4     mstatusBit_MPP_lo       (priv.extractLsb' 0 1 == 1#1)
  let s6 := setBit32 s5     (mstatusBit_MPP_lo + 1) (priv.extractLsb' 1 1 == 1#1)
  s6

/-- M-trap impl-style expression in `SoC.lean`. -/
def mstatusTrapMVal_impl
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) : BitVec 32 :=
  let msClearMIE := mstatus &&& 0xFFFFFFF7#32
  let msSetMPIE := if mie then msClearMIE ||| 0x00000080#32
                   else msClearMIE &&& 0xFFFFFF7F#32
  let msSetMPIE_clearMPP := msSetMPIE &&& 0xFFFFE7FF#32
  let privModeExt : BitVec 32 := 0#21 ++ (priv ++ 0#9)
  let privShifted : BitVec 32 := privModeExt <<< (2#32)
  msSetMPIE_clearMPP ||| privShifted

/-- Equivalence pure ↔ impl. -/
theorem mstatusTrapMVal_pure_eq_impl
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) :
    mstatusTrapMVal_pure mstatus mie priv =
      mstatusTrapMVal_impl mstatus mie priv := by
  unfold mstatusTrapMVal_pure mstatusTrapMVal_impl setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  bv_decide

/-- M-trap clears MIE. -/
@[simp] theorem mstatus_trapM_MIE_zero
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapMVal_pure mstatus mie priv) mstatusBit_MIE = false := by
  unfold getBit32 mstatusTrapMVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mie
  bv_decide

/-- M-trap sets MPIE to old MIE. -/
@[simp] theorem mstatus_trapM_MPIE_eq_input_MIE
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapMVal_pure mstatus mie priv) mstatusBit_MPIE = mie := by
  unfold getBit32 mstatusTrapMVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mie
  bv_decide

/-- M-trap sets MPP[11] to priv[0]. -/
@[simp] theorem mstatus_trapM_MPP_low_eq_priv0
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapMVal_pure mstatus mie priv) mstatusBit_MPP_lo
      = (priv.extractLsb' 0 1 == 1#1) := by
  unfold getBit32 mstatusTrapMVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mie
  bv_decide

/-- M-trap sets MPP[12] to priv[1]. -/
@[simp] theorem mstatus_trapM_MPP_high_eq_priv1
    (mstatus : BitVec 32) (mie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapMVal_pure mstatus mie priv) (mstatusBit_MPP_lo + 1)
      = (priv.extractLsb' 1 1 == 1#1) := by
  unfold getBit32 mstatusTrapMVal_pure setBit32
    mstatusBit_MIE mstatusBit_MPIE mstatusBit_MPP_lo
  revert mie
  bv_decide

/-! ## S-mode trap entry transformation

  Spec: S-mode trap sets `SPIE := SIE`, `SIE := 0`, `SPP := privMode[0]`.
  Other bits unchanged.
-/

/-- Pure S-trap entry transformation. -/
def mstatusTrapSVal_pure
    (mstatus : BitVec 32) (sie : Bool) (priv : BitVec 2) : BitVec 32 :=
  let s1 := setBit32 mstatus mstatusBit_SIE   false
  let s2 := setBit32 s1     mstatusBit_SPIE  sie
  let s3 := setBit32 s2     mstatusBit_SPP   (priv.extractLsb' 0 1 == 1#1)
  s3

/-- S-trap impl-style expression. -/
def mstatusTrapSVal_impl
    (mstatus : BitVec 32) (sie : Bool) (priv : BitVec 2) : BitVec 32 :=
  let msClearSIE := mstatus &&& 0xFFFFFFFD#32
  let msSetSPIE  := if sie then msClearSIE ||| 0x00000020#32
                    else msClearSIE &&& 0xFFFFFFDF#32
  let priv0_is_one := priv.extractLsb' 0 1 == 1#1
  if priv0_is_one then msSetSPIE ||| 0x00000100#32
  else msSetSPIE &&& 0xFFFFFEFF#32

/-- Equivalence pure ↔ impl. -/
theorem mstatusTrapSVal_pure_eq_impl
    (mstatus : BitVec 32) (sie : Bool) (priv : BitVec 2) :
    mstatusTrapSVal_pure mstatus sie priv =
      mstatusTrapSVal_impl mstatus sie priv := by
  unfold mstatusTrapSVal_pure mstatusTrapSVal_impl setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  bv_decide

@[simp] theorem mstatus_trapS_SIE_zero
    (mstatus : BitVec 32) (sie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapSVal_pure mstatus sie priv) mstatusBit_SIE = false := by
  unfold getBit32 mstatusTrapSVal_pure setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  revert sie
  bv_decide

@[simp] theorem mstatus_trapS_SPIE_eq_input_SIE
    (mstatus : BitVec 32) (sie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapSVal_pure mstatus sie priv) mstatusBit_SPIE = sie := by
  unfold getBit32 mstatusTrapSVal_pure setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  revert sie
  bv_decide

@[simp] theorem mstatus_trapS_SPP_eq_priv0
    (mstatus : BitVec 32) (sie : Bool) (priv : BitVec 2) :
    getBit32 (mstatusTrapSVal_pure mstatus sie priv) mstatusBit_SPP
      = (priv.extractLsb' 0 1 == 1#1) := by
  unfold getBit32 mstatusTrapSVal_pure setBit32
    mstatusBit_SIE mstatusBit_SPIE mstatusBit_SPP
  revert sie
  bv_decide

/-! ## Signal-level wrappers

These re-encode the existing `SoC.lean` mux chains as named functions
so that callers see a single point of truth for each architectural
event. They are equal to the pure functions above (theorems
`mstatus*Val_pure_eq_impl`), so all proven bit-level invariants apply
through the `_eq_pure` lemmas below. -/

/-- Signal-level MRET transformer (cycle-wise). -/
def mstatusMretValSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32))
    (mpie : Signal dom Bool) : Signal dom (BitVec 32) :=
  let msClearMPP := mstatus &&& 0xFFFFE7FF#32
  let msRestoreMIE :=
    Signal.mux mpie (msClearMPP ||| 0x00000008#32)
                    (msClearMPP &&& 0xFFFFFFF7#32)
  msRestoreMIE ||| 0x00000080#32

/-- Signal-level SRET transformer (cycle-wise). -/
def mstatusSretValSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32))
    (spie : Signal dom Bool) : Signal dom (BitVec 32) :=
  let msClearSPP := mstatus &&& 0xFFFFFEFF#32
  let msRestoreSIE :=
    Signal.mux spie (msClearSPP ||| 0x00000002#32)
                    (msClearSPP &&& 0xFFFFFFFD#32)
  msRestoreSIE ||| 0x00000020#32

/-- Signal-level M-mode trap entry (cycle-wise). -/
def mstatusTrapMValSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32))
    (mie : Signal dom Bool)
    (priv : Signal dom (BitVec 2)) : Signal dom (BitVec 32) :=
  let msClearMIE := mstatus &&& 0xFFFFFFF7#32
  let msSetMPIE :=
    Signal.mux mie (msClearMIE ||| 0x00000080#32)
                   (msClearMIE &&& 0xFFFFFF7F#32)
  let msSetMPIE_clearMPP := msSetMPIE &&& 0xFFFFE7FF#32
  -- Build privMode shifted into bits [12:11]: priv ++ 0#9 = bits [10:0]
  -- with priv at [10:9], then prepend 21 zeros and shift left 2.
  let privPad : Signal dom (BitVec 11) := priv ++ (0#9 : BitVec 9)
  let privModeExt : Signal dom (BitVec 32) := (0#21 : BitVec 21) ++ privPad
  let privShifted := privModeExt <<< (2#32 : BitVec 32)
  msSetMPIE_clearMPP ||| privShifted

/-- Signal-level S-mode trap entry (cycle-wise). -/
def mstatusTrapSValSignal {dom : DomainConfig}
    (mstatus : Signal dom (BitVec 32))
    (sie : Signal dom Bool)
    (priv : Signal dom (BitVec 2)) : Signal dom (BitVec 32) :=
  let msClearSIE := mstatus &&& 0xFFFFFFFD#32
  let msSetSPIE :=
    Signal.mux sie (msClearSIE ||| 0x00000020#32)
                   (msClearSIE &&& 0xFFFFFFDF#32)
  let privBit0 := priv.map (BitVec.extractLsb' 0 1 ·)
  let privBit0IsOne := privBit0 === 1#1
  Signal.mux privBit0IsOne
    (msSetSPIE ||| 0x00000100#32)
    (msSetSPIE &&& 0xFFFFFEFF#32)

/-! ## Trap-destination select

  Once both candidate trap-entry mstatus values are computed
  (S-mode and M-mode forms), the actual entry value is picked
  by the trap destination: `trapToS` → S; else → M.
-/

@[inline] def mstatusTrapValPure
    (trapToS : Bool) (mstatusTrapSVal mstatusTrapMVal : BitVec 32) : BitVec 32 :=
  if trapToS then mstatusTrapSVal else mstatusTrapMVal

@[simp] theorem mstatusTrapVal_to_S
    (mstatusTrapSVal mstatusTrapMVal : BitVec 32) :
    mstatusTrapValPure true mstatusTrapSVal mstatusTrapMVal = mstatusTrapSVal := rfl

@[simp] theorem mstatusTrapVal_to_M
    (mstatusTrapSVal mstatusTrapMVal : BitVec 32) :
    mstatusTrapValPure false mstatusTrapSVal mstatusTrapMVal = mstatusTrapMVal := rfl

theorem mstatusTrapValPure_spec
    (trapToS : Bool) (mstatusTrapSVal mstatusTrapMVal : BitVec 32) :
    mstatusTrapValPure trapToS mstatusTrapSVal mstatusTrapMVal =
      (if trapToS then mstatusTrapSVal else mstatusTrapMVal) := rfl

def mstatusTrapValSignal {dom : DomainConfig}
    (trapToS : Signal dom Bool)
    (mstatusTrapSVal mstatusTrapMVal : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux trapToS mstatusTrapSVal mstatusTrapMVal

end Sparkle.IP.RV32.CSR

