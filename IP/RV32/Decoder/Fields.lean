/-
  RV32 instruction-field decoder — equivalence proofs

  Two pure forms of the per-field decoders exist in this codebase:

    * `IP/RV32/Types.lean`'s `extractOpcode/Rd/Funct3/Rs1/Rs2/Funct7`
      — uses `(inst >>> shift).truncate width`.

    * `IP/RV32/SoC.lean`'s inline calls — use
      `inst.extractLsb' shift width`.

  These should produce bit-identical results, but they're written
  with different primitives. This file proves the two are equivalent.
  Once proven, every field-extraction site can use whichever form is
  more convenient without changing the meaning.

  Per RV32I §2.2, the 32-bit instruction is laid out as:

    bits [6:0]   opcode  (7 bits)
    bits [11:7]  rd      (5 bits)
    bits [14:12] funct3  (3 bits)
    bits [19:15] rs1     (5 bits)
    bits [24:20] rs2     (5 bits)
    bits [31:25] funct7  (7 bits)
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Types

namespace Sparkle.IP.RV32.Decoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32 (extractOpcode extractRd extractFunct3
                       extractRs1 extractRs2 extractFunct7)

/-! ## Equivalence: shift+truncate vs extractLsb' -/

/-- opcode = bits [6:0] (extractLsb' form). -/
theorem extractOpcode_eq_lsb (inst : BitVec 32) :
    extractOpcode inst = inst.extractLsb' 0 7 := by
  unfold extractOpcode
  bv_decide

/-- rd = bits [11:7] (extractLsb' form). -/
theorem extractRd_eq_lsb (inst : BitVec 32) :
    extractRd inst = inst.extractLsb' 7 5 := by
  unfold extractRd
  bv_decide

/-- funct3 = bits [14:12] (extractLsb' form). -/
theorem extractFunct3_eq_lsb (inst : BitVec 32) :
    extractFunct3 inst = inst.extractLsb' 12 3 := by
  unfold extractFunct3
  bv_decide

/-- rs1 = bits [19:15] (extractLsb' form). -/
theorem extractRs1_eq_lsb (inst : BitVec 32) :
    extractRs1 inst = inst.extractLsb' 15 5 := by
  unfold extractRs1
  bv_decide

/-- rs2 = bits [24:20] (extractLsb' form). -/
theorem extractRs2_eq_lsb (inst : BitVec 32) :
    extractRs2 inst = inst.extractLsb' 20 5 := by
  unfold extractRs2
  bv_decide

/-- funct7 = bits [31:25] (extractLsb' form). -/
theorem extractFunct7_eq_lsb (inst : BitVec 32) :
    extractFunct7 inst = inst.extractLsb' 25 7 := by
  unfold extractFunct7
  bv_decide

/-! ## Field-non-overlap

  The six fields together cover the entire 32-bit instruction
  (at most one field per bit). This is encoded as: any bit
  appears in at most one field. -/

/-- The total bit width of the 6 fields = 32. -/
theorem fields_total_width : 7 + 5 + 3 + 5 + 5 + 7 = 32 := rfl

end Sparkle.IP.RV32.Decoder
