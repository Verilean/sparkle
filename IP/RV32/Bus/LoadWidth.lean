/-
  RV32 sub-word load extractor — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 778..819). Maps a
  32-bit bus rdata to the loaded value, given:
    * The low two bits of the effective address (`addr[1:0]`).
    * The funct3 decoded into LB/LH/LBU/LHU/LW.

  Three pieces:
    1. **Byte select**: `selByte addr[1:0] busRdata = busRdata[7:0]`
       at byte position `addr[1:0]`.
    2. **Half select**: `selHalf addr[1] busRdata = busRdata[15:0]` at
       halfword position `addr[1]`.
    3. **Sign/zero extension** to 32 bits, then a 5-way mux on funct3
       picks the final result (LW = full word, no extraction).

  Spec (RISC-V unprivileged spec, §2.6 Loads and Stores):

    funct3 | mnemonic | extension     | extraction
    -------|----------|---------------|---------------------
    000    | LB       | sign-ext byte | byte at addr[1:0]
    001    | LH       | sign-ext half | half at addr[1]
    010    | LW       | (none)        | full 32-bit word
    100    | LBU      | zero-ext byte | byte at addr[1:0]
    101    | LHU      | zero-ext half | half at addr[1]
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure byte / half select -/

/-- Select the byte at position `off` (in [0,4)) from a 32-bit word. -/
@[inline] def selBytePure
    (off0 off1 off2 : Bool) (busRdata : BitVec 32) : BitVec 8 :=
  let b0 := busRdata.extractLsb' 0 8
  let b1 := busRdata.extractLsb' 8 8
  let b2 := busRdata.extractLsb' 16 8
  let b3 := busRdata.extractLsb' 24 8
  if off0 then b0
  else if off1 then b1
  else if off2 then b2
  else b3

/-- Select the halfword at position `addr[1]` (0 = low, 1 = high). -/
@[inline] def selHalfPure (isLow : Bool) (busRdata : BitVec 32) : BitVec 16 :=
  if isLow then busRdata.extractLsb' 0 16
  else busRdata.extractLsb' 16 16

/-! ## Sign / zero extension to BitVec 32 -/

/-- Sign-extend a byte to 32 bits. -/
@[inline] def sextBytePure (b : BitVec 8) : BitVec 32 :=
  let signBit := b.extractLsb' 7 1
  let high24 : BitVec 24 := if signBit = 1#1 then 0xFFFFFF#24 else 0#24
  high24 ++ b

/-- Zero-extend a byte to 32 bits. -/
@[inline] def zextBytePure (b : BitVec 8) : BitVec 32 :=
  (0#24 : BitVec 24) ++ b

/-- Sign-extend a halfword to 32 bits. -/
@[inline] def sextHalfPure (h : BitVec 16) : BitVec 32 :=
  let signBit := h.extractLsb' 15 1
  let high16 : BitVec 16 := if signBit = 1#1 then 0xFFFF#16 else 0#16
  high16 ++ h

/-- Zero-extend a halfword to 32 bits. -/
@[inline] def zextHalfPure (h : BitVec 16) : BitVec 32 :=
  (0#16 : BitVec 16) ++ h

/-! ## funct3 → loadExtracted selector -/

/-- 5-way selector picking the final 32-bit load result.
    Priority: LB > LH > LBU > LHU > (default = full word LW). -/
@[inline] def loadExtractPure
    (isLB isLH isLBU isLHU : Bool)
    (byteSext byteZext halfSext halfZext busRdata : BitVec 32) : BitVec 32 :=
  if isLB then byteSext
  else if isLH then halfSext
  else if isLBU then byteZext
  else if isLHU then halfZext
  else busRdata

/-! ## Spec invariants -/

/-- Byte at offset 0 is the LSB byte. -/
@[simp] theorem selByte_off0
    (off1 off2 : Bool) (busRdata : BitVec 32) :
    selBytePure true off1 off2 busRdata = busRdata.extractLsb' 0 8 := by
  rfl

/-- Byte at offset 1 is bytes [15:8]. -/
@[simp] theorem selByte_off1
    (off2 : Bool) (busRdata : BitVec 32) :
    selBytePure false true off2 busRdata = busRdata.extractLsb' 8 8 := by
  rfl

/-- Byte at offset 2 is bytes [23:16]. -/
@[simp] theorem selByte_off2 (busRdata : BitVec 32) :
    selBytePure false false true busRdata = busRdata.extractLsb' 16 8 := by
  rfl

/-- Byte at offset 3 (default) is bytes [31:24]. -/
@[simp] theorem selByte_off3 (busRdata : BitVec 32) :
    selBytePure false false false busRdata = busRdata.extractLsb' 24 8 := by
  rfl

/-- Half at addr[1]=0 is the low halfword. -/
@[simp] theorem selHalf_low (busRdata : BitVec 32) :
    selHalfPure true busRdata = busRdata.extractLsb' 0 16 := by
  rfl

/-- Half at addr[1]=1 is the high halfword. -/
@[simp] theorem selHalf_high (busRdata : BitVec 32) :
    selHalfPure false busRdata = busRdata.extractLsb' 16 16 := by
  rfl

/-- LB picks the sign-extended byte. -/
@[simp] theorem loadExtract_LB
    (isLH isLBU isLHU : Bool)
    (byteSext byteZext halfSext halfZext busRdata : BitVec 32) :
    loadExtractPure true isLH isLBU isLHU
      byteSext byteZext halfSext halfZext busRdata = byteSext := by
  rfl

/-- LH picks the sign-extended halfword (when LB is clear). -/
@[simp] theorem loadExtract_LH
    (isLBU isLHU : Bool)
    (byteSext byteZext halfSext halfZext busRdata : BitVec 32) :
    loadExtractPure false true isLBU isLHU
      byteSext byteZext halfSext halfZext busRdata = halfSext := by
  rfl

/-- LBU picks the zero-extended byte. -/
@[simp] theorem loadExtract_LBU
    (isLHU : Bool)
    (byteSext byteZext halfSext halfZext busRdata : BitVec 32) :
    loadExtractPure false false true isLHU
      byteSext byteZext halfSext halfZext busRdata = byteZext := by
  rfl

/-- LHU picks the zero-extended halfword. -/
@[simp] theorem loadExtract_LHU
    (byteSext byteZext halfSext halfZext busRdata : BitVec 32) :
    loadExtractPure false false false true
      byteSext byteZext halfSext halfZext busRdata = halfZext := by
  rfl

/-- LW (default, no funct3 match) returns the full bus word. -/
@[simp] theorem loadExtract_LW
    (byteSext byteZext halfSext halfZext busRdata : BitVec 32) :
    loadExtractPure false false false false
      byteSext byteZext halfSext halfZext busRdata = busRdata := by
  rfl

/-! ## Bit-level invariants — closed by `bv_decide` -/

/-- LBU result has zero high 24 bits. -/
theorem zextByte_high_zero (b : BitVec 8) :
    (zextBytePure b).extractLsb' 8 24 = 0#24 := by
  unfold zextBytePure
  bv_decide

/-- LHU result has zero high 16 bits. -/
theorem zextHalf_high_zero (h : BitVec 16) :
    (zextHalfPure h).extractLsb' 16 16 = 0#16 := by
  unfold zextHalfPure
  bv_decide

/-- LBU result low 8 bits are the input byte. -/
theorem zextByte_low_eq (b : BitVec 8) :
    (zextBytePure b).extractLsb' 0 8 = b := by
  unfold zextBytePure
  bv_decide

/-- LHU result low 16 bits are the input halfword. -/
theorem zextHalf_low_eq (h : BitVec 16) :
    (zextHalfPure h).extractLsb' 0 16 = h := by
  unfold zextHalfPure
  bv_decide

/-- LB result's low 8 bits are the input byte. -/
theorem sextByte_low_eq (b : BitVec 8) :
    (sextBytePure b).extractLsb' 0 8 = b := by
  unfold sextBytePure
  cases h : b.extractLsb' 7 1 == 1#1 <;>
  · simp
    bv_decide

/-- LH result low 16 bits are the input halfword. -/
theorem sextHalf_low_eq (h : BitVec 16) :
    (sextHalfPure h).extractLsb' 0 16 = h := by
  unfold sextHalfPure
  cases hb : h.extractLsb' 15 1 == 1#1 <;>
  · simp
    bv_decide

/-! ## Composite spec — exhaustive over Bool^4 -/

/-- `loadExtractPure` is the canonical 5-way priority mux. -/
theorem loadExtractPure_spec :
    ∀ (isLB isLH isLBU isLHU : Bool)
      (byteSext byteZext halfSext halfZext busRdata : BitVec 32),
      loadExtractPure isLB isLH isLBU isLHU
        byteSext byteZext halfSext halfZext busRdata =
          (if isLB then byteSext
           else if isLH then halfSext
           else if isLBU then byteZext
           else if isLHU then halfZext
           else busRdata) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def selByteSignal {dom : DomainConfig}
    (off0 off1 off2 : Signal dom Bool)
    (busRdata : Signal dom (BitVec 32)) : Signal dom (BitVec 8) :=
  let b0 := busRdata.map (BitVec.extractLsb' 0 8 ·)
  let b1 := busRdata.map (BitVec.extractLsb' 8 8 ·)
  let b2 := busRdata.map (BitVec.extractLsb' 16 8 ·)
  let b3 := busRdata.map (BitVec.extractLsb' 24 8 ·)
  Signal.mux off0 b0
    (Signal.mux off1 b1
      (Signal.mux off2 b2 b3))

def selHalfSignal {dom : DomainConfig}
    (isLow : Signal dom Bool)
    (busRdata : Signal dom (BitVec 32)) : Signal dom (BitVec 16) :=
  Signal.mux isLow
    (busRdata.map (BitVec.extractLsb' 0 16 ·))
    (busRdata.map (BitVec.extractLsb' 16 16 ·))

def loadExtractSignal {dom : DomainConfig}
    (isLB isLH isLBU isLHU : Signal dom Bool)
    (byteSext byteZext halfSext halfZext busRdata : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux isLB byteSext
    (Signal.mux isLH halfSext
    (Signal.mux isLBU byteZext
    (Signal.mux isLHU halfZext busRdata)))

end Sparkle.IP.RV32.Bus
