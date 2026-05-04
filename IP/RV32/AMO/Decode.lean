/-
  RV32 AMO opcode decoder — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1158..1162). The AMO
  ("Atomic Memory Operation") instructions all share opcode
  0b0101111 (= 0x2F). The funct7[6:2] field (= inst[31:27])
  selects which AMO operation:

    funct7[6:2]  mnemonic
    -----------  -----------
    00010        LR.W       (load-reserved)
    00011        SC.W       (store-conditional)
    00001        AMOSWAP.W
    00000        AMOADD.W
    00100        AMOXOR.W
    01100        AMOAND.W
    01000        AMOOR.W
    10000        AMOMIN.W
    10100        AMOMAX.W
    11000        AMOMINU.W
    11100        AMOMAXU.W

  Sparkle decodes:
    isAMO   = (opcode == 0x2F)
    isLR    = isAMO ∧ (amoOp == 00010)
    isSC    = isAMO ∧ (amoOp == 00011)
    isAMOrw = isAMO ∧ ¬(isLR ∨ isSC)   -- swap/add/xor/and/or/min/max
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.AMO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure AMO opcode decoders -/

/-- AMO opcode field (funct7[6:2] = inst[31:27]). -/
@[inline] def amoOpPure (inst : BitVec 32) : BitVec 5 :=
  inst.extractLsb' 27 5

/-- isAMO: top-level opcode == 0b0101111. -/
@[inline] def isAMOPure (opcode : BitVec 7) : Bool :=
  opcode == 0b0101111#7

/-- isLR: load-reserved (amoOp == 00010). -/
@[inline] def isLRPure (opcode : BitVec 7) (amoOp : BitVec 5) : Bool :=
  isAMOPure opcode && (amoOp == 0b00010#5)

/-- isSC: store-conditional (amoOp == 00011). -/
@[inline] def isSCPure (opcode : BitVec 7) (amoOp : BitVec 5) : Bool :=
  isAMOPure opcode && (amoOp == 0b00011#5)

/-- isAMOrw: read-modify-write AMO (any AMO that's not LR/SC). -/
@[inline] def isAMOrwPure (opcode : BitVec 7) (amoOp : BitVec 5) : Bool :=
  isAMOPure opcode && !(isLRPure opcode amoOp || isSCPure opcode amoOp)

/-! ## Spec invariants — closed by `decide` / `bv_decide` -/

/-- Non-AMO opcode → all AMO-class predicates are false. -/
theorem amo_class_clear_for_non_amo
    (opcode : BitVec 7) (amoOp : BitVec 5)
    (h : isAMOPure opcode = false) :
    isLRPure opcode amoOp = false ∧
    isSCPure opcode amoOp = false ∧
    isAMOrwPure opcode amoOp = false := by
  unfold isLRPure isSCPure isAMOrwPure
  rw [h]
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- AMO opcode + amoOp=00010 → isLR. -/
theorem isLR_fires (amoOp : BitVec 5) (h : amoOp = 0b00010#5) :
    isLRPure 0b0101111#7 amoOp = true := by
  unfold isLRPure isAMOPure
  rw [h]
  rfl

/-- AMO opcode + amoOp=00011 → isSC. -/
theorem isSC_fires (amoOp : BitVec 5) (h : amoOp = 0b00011#5) :
    isSCPure 0b0101111#7 amoOp = true := by
  unfold isSCPure isAMOPure
  rw [h]
  rfl

/-- LR and SC are mutually exclusive (different amoOp values). -/
theorem isLR_isSC_mutex (opcode : BitVec 7) (amoOp : BitVec 5) :
    !(isLRPure opcode amoOp && isSCPure opcode amoOp) = true := by
  unfold isLRPure isSCPure isAMOPure
  revert opcode amoOp; bv_decide

/-- LR and AMOrw are mutually exclusive — AMOrw excludes LR by definition. -/
theorem isLR_isAMOrw_mutex (opcode : BitVec 7) (amoOp : BitVec 5) :
    !(isLRPure opcode amoOp && isAMOrwPure opcode amoOp) = true := by
  unfold isAMOrwPure
  -- AMOrw has !(isLR ∨ isSC) gating, so isLR ∧ AMOrw ⇒ isLR ∧ !isLR.
  cases h_lr : isLRPure opcode amoOp <;> simp [h_lr]

/-- SC and AMOrw are mutually exclusive — AMOrw excludes SC by definition. -/
theorem isSC_isAMOrw_mutex (opcode : BitVec 7) (amoOp : BitVec 5) :
    !(isSCPure opcode amoOp && isAMOrwPure opcode amoOp) = true := by
  unfold isAMOrwPure
  cases h_sc : isSCPure opcode amoOp <;> simp [h_sc]

/-- AMOSWAP (amoOp=00001) is an AMOrw, not LR or SC. -/
theorem isAMOrw_swap :
    isAMOrwPure 0b0101111#7 0b00001#5 = true := by
  unfold isAMOrwPure isAMOPure isLRPure isSCPure
  decide

/-- AMOADD (amoOp=00000) is an AMOrw. -/
theorem isAMOrw_add :
    isAMOrwPure 0b0101111#7 0b00000#5 = true := by
  unfold isAMOrwPure isAMOPure isLRPure isSCPure
  decide

/-! ## Composite specs -/

theorem isAMOPure_spec (opcode : BitVec 7) :
    isAMOPure opcode = (opcode == 0b0101111#7) := by rfl

theorem isLRPure_spec (opcode : BitVec 7) (amoOp : BitVec 5) :
    isLRPure opcode amoOp =
      ((opcode == 0b0101111#7) && (amoOp == 0b00010#5)) := by rfl

theorem isSCPure_spec (opcode : BitVec 7) (amoOp : BitVec 5) :
    isSCPure opcode amoOp =
      ((opcode == 0b0101111#7) && (amoOp == 0b00011#5)) := by rfl

/-! ## Signal-level wrappers -/

def amoOpSignal {dom : DomainConfig}
    (inst : Signal dom (BitVec 32)) : Signal dom (BitVec 5) :=
  inst.map (BitVec.extractLsb' 27 5 ·)

def isAMOSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b0101111#7

def isLRSignal {dom : DomainConfig}
    (isAMO : Signal dom Bool) (amoOp : Signal dom (BitVec 5))
    : Signal dom Bool :=
  isAMO &&& (amoOp === 0b00010#5)

def isSCSignal {dom : DomainConfig}
    (isAMO : Signal dom Bool) (amoOp : Signal dom (BitVec 5))
    : Signal dom Bool :=
  isAMO &&& (amoOp === 0b00011#5)

def isAMOrwSignal {dom : DomainConfig}
    (isAMO isLR isSC : Signal dom Bool) : Signal dom Bool :=
  isAMO &&& (~~~(isLR ||| isSC))

end Sparkle.IP.RV32.AMO
