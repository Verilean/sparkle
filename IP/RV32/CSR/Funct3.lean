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

end Sparkle.IP.RV32.CSR
