/-
  RV32 CSR funct3 decoder — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1398..1404). The CSR
  instructions (Zicsr extension) use funct3 to encode both:
    1. The op (RW = csrrw, RS = csrrs, RC = csrrc)
    2. Whether to use a 5-bit zero-extended immediate from rs1Idx
       (csrr*i variants) instead of the rs1 register value

  Per RISC-V Zicsr §6 (Zicsr instructions), funct3 encoding:

    funct3   variant   semantics
    ------   -------   -----------------
    001      CSRRW     R/W with rs1
    010      CSRRS     R/S with rs1
    011      CSRRC     R/C with rs1
    101      CSRRWI    R/W with imm (zero-ext rs1Idx)
    110      CSRRSI    R/S with imm
    111      CSRRCI    R/C with imm

  Decomposing funct3 by bit position:

    funct3[2]   1 = use immediate (csrr*i), 0 = use rs1
    funct3[1:0] 01 = RW, 10 = RS, 11 = RC, 00 = invalid

  This file proves the per-bit decoders and the standard 6-way
  encoding spec.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure CSR funct3 decoders -/

/-- csrIsImm: bit 2 of funct3 — true for csrr*i variants. -/
@[inline] def csrIsImmPure (funct3 : BitVec 3) : Bool :=
  funct3.extractLsb' 2 1 == 1#1

/-- Lower 2 bits of funct3 — selects RW/RS/RC. -/
@[inline] def csrF3LowPure (funct3 : BitVec 3) : BitVec 2 :=
  funct3.extractLsb' 0 2

/-- csrIsRW: lower-2 bits == 01. -/
@[inline] def csrIsRWPure (funct3 : BitVec 3) : Bool :=
  csrF3LowPure funct3 == 0b01#2

/-- csrIsRS: lower-2 bits == 10. -/
@[inline] def csrIsRSPure (funct3 : BitVec 3) : Bool :=
  csrF3LowPure funct3 == 0b10#2

/-- csrIsRC: lower-2 bits == 11. -/
@[inline] def csrIsRCPure (funct3 : BitVec 3) : Bool :=
  csrF3LowPure funct3 == 0b11#2

/-! ## Per-encoding spec — closed by `bv_decide` -/

/-- CSRRW (funct3 = 001): not imm, RW. -/
theorem csrFunct3_CSRRW :
    csrIsImmPure 0b001#3 = false ∧
    csrIsRWPure 0b001#3 = true ∧
    csrIsRSPure 0b001#3 = false ∧
    csrIsRCPure 0b001#3 = false := by
  unfold csrIsImmPure csrIsRWPure csrIsRSPure csrIsRCPure csrF3LowPure
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- CSRRS (funct3 = 010): not imm, RS. -/
theorem csrFunct3_CSRRS :
    csrIsImmPure 0b010#3 = false ∧
    csrIsRWPure 0b010#3 = false ∧
    csrIsRSPure 0b010#3 = true ∧
    csrIsRCPure 0b010#3 = false := by
  unfold csrIsImmPure csrIsRWPure csrIsRSPure csrIsRCPure csrF3LowPure
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- CSRRC (funct3 = 011): not imm, RC. -/
theorem csrFunct3_CSRRC :
    csrIsImmPure 0b011#3 = false ∧
    csrIsRWPure 0b011#3 = false ∧
    csrIsRSPure 0b011#3 = false ∧
    csrIsRCPure 0b011#3 = true := by
  unfold csrIsImmPure csrIsRWPure csrIsRSPure csrIsRCPure csrF3LowPure
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- CSRRWI (funct3 = 101): imm, RW. -/
theorem csrFunct3_CSRRWI :
    csrIsImmPure 0b101#3 = true ∧
    csrIsRWPure 0b101#3 = true ∧
    csrIsRSPure 0b101#3 = false ∧
    csrIsRCPure 0b101#3 = false := by
  unfold csrIsImmPure csrIsRWPure csrIsRSPure csrIsRCPure csrF3LowPure
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- CSRRSI (funct3 = 110): imm, RS. -/
theorem csrFunct3_CSRRSI :
    csrIsImmPure 0b110#3 = true ∧
    csrIsRWPure 0b110#3 = false ∧
    csrIsRSPure 0b110#3 = true ∧
    csrIsRCPure 0b110#3 = false := by
  unfold csrIsImmPure csrIsRWPure csrIsRSPure csrIsRCPure csrF3LowPure
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- CSRRCI (funct3 = 111): imm, RC. -/
theorem csrFunct3_CSRRCI :
    csrIsImmPure 0b111#3 = true ∧
    csrIsRWPure 0b111#3 = false ∧
    csrIsRSPure 0b111#3 = false ∧
    csrIsRCPure 0b111#3 = true := by
  unfold csrIsImmPure csrIsRWPure csrIsRSPure csrIsRCPure csrF3LowPure
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-! ## Mutual exclusion + completeness -/

/-- RW/RS pairwise mutex. -/
theorem csrOps_RW_RS_mutex (funct3 : BitVec 3) :
    !(csrIsRWPure funct3 && csrIsRSPure funct3) = true := by
  unfold csrIsRWPure csrIsRSPure csrF3LowPure
  revert funct3; bv_decide

/-- RW/RC pairwise mutex. -/
theorem csrOps_RW_RC_mutex (funct3 : BitVec 3) :
    !(csrIsRWPure funct3 && csrIsRCPure funct3) = true := by
  unfold csrIsRWPure csrIsRCPure csrF3LowPure
  revert funct3; bv_decide

/-- RS/RC pairwise mutex. -/
theorem csrOps_RS_RC_mutex (funct3 : BitVec 3) :
    !(csrIsRSPure funct3 && csrIsRCPure funct3) = true := by
  unfold csrIsRSPure csrIsRCPure csrF3LowPure
  revert funct3; bv_decide

/-! ## Composite specs -/

theorem csrIsImmPure_spec (funct3 : BitVec 3) :
    csrIsImmPure funct3 = (funct3.extractLsb' 2 1 == 1#1) := by rfl

theorem csrIsRWPure_spec (funct3 : BitVec 3) :
    csrIsRWPure funct3 = (funct3.extractLsb' 0 2 == 0b01#2) := by rfl

/-! ## Signal-level wrappers -/

def csrIsImmSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  (funct3.map (BitVec.extractLsb' 2 1 ·)) === 1#1

def csrF3LowSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom (BitVec 2) :=
  funct3.map (BitVec.extractLsb' 0 2 ·)

def csrIsRWSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  csrF3LowSignal funct3 === 0b01#2

def csrIsRSSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  csrF3LowSignal funct3 === 0b10#2

def csrIsRCSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  csrF3LowSignal funct3 === 0b11#2

/-! ## CSR write-data formation

  CSR writes can come from one of two sources, distinguished by
  csrIsImm:

    csrIsImm = funct3[2] = 1  →  CSRRWI/CSRRSI/CSRRCI: 5-bit zimm,
                                  zero-extended to 32 bits
              ¬csrIsImm       →  CSRRW/CSRRS/CSRRC: rs1 register value

  The zimm reuses the rs1Idx field of the instruction as a 5-bit
  immediate.
-/

@[inline] def csrZimmPure (rs1Idx : BitVec 5) : BitVec 32 :=
  (0#27 : BitVec 27) ++ rs1Idx

@[inline] def csrWdataPure
    (csrIsImm : Bool) (csrZimm ex_rs1 : BitVec 32) : BitVec 32 :=
  if csrIsImm then csrZimm else ex_rs1

@[simp] theorem csrWdata_imm (csrZimm ex_rs1 : BitVec 32) :
    csrWdataPure true csrZimm ex_rs1 = csrZimm := rfl

@[simp] theorem csrWdata_reg (csrZimm ex_rs1 : BitVec 32) :
    csrWdataPure false csrZimm ex_rs1 = ex_rs1 := rfl

theorem csrWdataPure_spec
    (csrIsImm : Bool) (csrZimm ex_rs1 : BitVec 32) :
    csrWdataPure csrIsImm csrZimm ex_rs1 =
      (if csrIsImm then csrZimm else ex_rs1) := rfl

/-- csrZimm has zero bits in [31:5]. -/
theorem csrZimm_high_zero (rs1Idx : BitVec 5) :
    (csrZimmPure rs1Idx).extractLsb' 5 27 = 0#27 := by
  unfold csrZimmPure
  bv_decide

/-- csrZimm preserves rs1Idx in low 5 bits. -/
theorem csrZimm_low_eq (rs1Idx : BitVec 5) :
    (csrZimmPure rs1Idx).extractLsb' 0 5 = rs1Idx := by
  unfold csrZimmPure
  bv_decide

def csrZimmSignal {dom : DomainConfig}
    (rs1Idx : Signal dom (BitVec 5)) : Signal dom (BitVec 32) :=
  let zero27 : Signal dom (BitVec 27) := Signal.pure 0#27
  zero27 ++ rs1Idx

def csrWdataSignal {dom : DomainConfig}
    (csrIsImm : Signal dom Bool)
    (csrZimm ex_rs1 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux csrIsImm csrZimm ex_rs1

end Sparkle.IP.RV32.CSR
