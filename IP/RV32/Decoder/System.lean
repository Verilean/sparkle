/-
  RV32 SYSTEM-instruction decoder — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1130..1156). Decodes the
  SYSTEM-opcode (0x73) family + the M-extension dispatch:

    Top-level opcode 0b1110011 (SYSTEM) sub-encodes by funct3+funct12:
      funct3=0 ∧ funct12=0x000 → ECALL
      funct3=0 ∧ funct12=0x302 → MRET
      funct3=0 ∧ funct12=0x102 → SRET
      funct3=0 ∧ funct7=0x09   → SFENCE.VMA  (sub-encoded via funct7)
      funct3≠0                  → CSR (csrrw/csrrs/csrrc + imm forms)

    M-extension: R-type opcode 0b0110011 + funct7=0b0000001 selects
    MUL/MULH/MULHSU/MULHU/DIV/DIVU/REM/REMU.

  The boolean predicates returned here are mutually exclusive
  in pairs (an instruction is at most one of MRET/SRET/ECALL/...).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Decoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure decoders -/

/-- isSystem: opcode == 0x73. -/
@[inline] def isSystemPure (opcode : BitVec 7) : Bool :=
  opcode == 0b1110011#7

/-- isCSR: SYSTEM + funct3 ≠ 0. -/
@[inline] def isCsrPure (opcode : BitVec 7) (funct3 : BitVec 3) : Bool :=
  isSystemPure opcode && !(funct3 == 0#3)

/-- isEcall: SYSTEM + funct3=0 + funct12=0x000. -/
@[inline] def isEcallPure
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) : Bool :=
  isSystemPure opcode && (funct3 == 0#3) && (funct12 == 0x000#12)

/-- isMret: SYSTEM + funct3=0 + funct12=0x302. -/
@[inline] def isMretPure
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) : Bool :=
  isSystemPure opcode && (funct3 == 0#3) && (funct12 == 0x302#12)

/-- isSret: SYSTEM + funct3=0 + funct12=0x102. -/
@[inline] def isSretPure
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) : Bool :=
  isSystemPure opcode && (funct3 == 0#3) && (funct12 == 0x102#12)

/-- isSFenceVMA: SYSTEM + funct3=0 + funct7=0b0001001. -/
@[inline] def isSFenceVMAPure
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct7 : BitVec 7) : Bool :=
  isSystemPure opcode && (funct3 == 0#3) && (funct7 == 0b0001001#7)

/-- isMext: R-type + funct7=0b0000001. -/
@[inline] def isMextPure
    (opcode : BitVec 7) (funct7 : BitVec 7) : Bool :=
  (opcode == 0b0110011#7) && (funct7 == 0b0000001#7)

/-! ## Spec invariants — closed by `bv_decide` -/

/-- Non-SYSTEM opcode → none of the SYSTEM predicates fire. -/
theorem system_clear_for_non_system
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12)
    (funct7 : BitVec 7) (h : isSystemPure opcode = false) :
    isCsrPure opcode funct3 = false ∧
    isEcallPure opcode funct3 funct12 = false ∧
    isMretPure opcode funct3 funct12 = false ∧
    isSretPure opcode funct3 funct12 = false ∧
    isSFenceVMAPure opcode funct3 funct7 = false := by
  unfold isCsrPure isEcallPure isMretPure isSretPure isSFenceVMAPure
  rw [h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- ECALL spec. -/
theorem isEcall_fires :
    isEcallPure 0b1110011#7 0#3 0x000#12 = true := by rfl

/-- MRET spec. -/
theorem isMret_fires :
    isMretPure 0b1110011#7 0#3 0x302#12 = true := by rfl

/-- SRET spec. -/
theorem isSret_fires :
    isSretPure 0b1110011#7 0#3 0x102#12 = true := by rfl

/-- SFENCE.VMA spec. -/
theorem isSFenceVMA_fires :
    isSFenceVMAPure 0b1110011#7 0#3 0b0001001#7 = true := by rfl

/-! ## Pairwise mutex (decided by `bv_decide`) -/

/-- ECALL and MRET are mutually exclusive (different funct12). -/
theorem ecall_mret_mutex
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) :
    !(isEcallPure opcode funct3 funct12 && isMretPure opcode funct3 funct12) = true := by
  unfold isEcallPure isMretPure isSystemPure
  revert opcode funct3 funct12; bv_decide

/-- ECALL and SRET are mutually exclusive. -/
theorem ecall_sret_mutex
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) :
    !(isEcallPure opcode funct3 funct12 && isSretPure opcode funct3 funct12) = true := by
  unfold isEcallPure isSretPure isSystemPure
  revert opcode funct3 funct12; bv_decide

/-- MRET and SRET are mutually exclusive. -/
theorem mret_sret_mutex
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) :
    !(isMretPure opcode funct3 funct12 && isSretPure opcode funct3 funct12) = true := by
  unfold isMretPure isSretPure isSystemPure
  revert opcode funct3 funct12; bv_decide

/-- isCSR and isEcall are mutually exclusive (CSR has funct3≠0, ECALL=0). -/
theorem csr_ecall_mutex
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) :
    !(isCsrPure opcode funct3 && isEcallPure opcode funct3 funct12) = true := by
  unfold isCsrPure isEcallPure isSystemPure
  revert opcode funct3 funct12; bv_decide

/-- isCSR and isMret are mutually exclusive. -/
theorem csr_mret_mutex
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct12 : BitVec 12) :
    !(isCsrPure opcode funct3 && isMretPure opcode funct3 funct12) = true := by
  unfold isCsrPure isMretPure isSystemPure
  revert opcode funct3 funct12; bv_decide

/-- isMext and isSystem are mutually exclusive (different opcodes). -/
theorem mext_system_mutex
    (opcode : BitVec 7) (funct3 : BitVec 3) (funct7 : BitVec 7) :
    !(isMextPure opcode funct7 && isCsrPure opcode funct3) = true := by
  unfold isMextPure isCsrPure isSystemPure
  revert opcode funct3 funct7; bv_decide

/-! ## Composite specs -/

theorem isSystemPure_spec (opcode : BitVec 7) :
    isSystemPure opcode = (opcode == 0b1110011#7) := by rfl

theorem isCsrPure_spec (opcode : BitVec 7) (funct3 : BitVec 3) :
    isCsrPure opcode funct3 =
      ((opcode == 0b1110011#7) && !(funct3 == 0#3)) := by rfl

/-! ## Signal-level wrappers -/

def isSystemSignal {dom : DomainConfig}
    (opcode : Signal dom (BitVec 7)) : Signal dom Bool :=
  opcode === 0b1110011#7

def isCsrSignal {dom : DomainConfig}
    (isSystem : Signal dom Bool) (funct3 : Signal dom (BitVec 3))
    : Signal dom Bool :=
  isSystem &&& (~~~(funct3 === 0#3))

def isEcallSignal {dom : DomainConfig}
    (isSystem : Signal dom Bool) (f3isZero : Signal dom Bool)
    (funct12 : Signal dom (BitVec 12)) : Signal dom Bool :=
  (isSystem &&& f3isZero) &&& (funct12 === 0x000#12)

def isMretSignal {dom : DomainConfig}
    (isSystem : Signal dom Bool) (f3isZero : Signal dom Bool)
    (funct12 : Signal dom (BitVec 12)) : Signal dom Bool :=
  (isSystem &&& f3isZero) &&& (funct12 === 0x302#12)

def isSretSignal {dom : DomainConfig}
    (isSystem : Signal dom Bool) (f3isZero : Signal dom Bool)
    (funct12 : Signal dom (BitVec 12)) : Signal dom Bool :=
  (isSystem &&& f3isZero) &&& (funct12 === 0x102#12)

def isSFenceVMASignal {dom : DomainConfig}
    (isSystem : Signal dom Bool) (f3isZero : Signal dom Bool)
    (funct7 : Signal dom (BitVec 7)) : Signal dom Bool :=
  (isSystem &&& f3isZero) &&& (funct7 === 0b0001001#7)

def isMextSignal {dom : DomainConfig}
    (isALUrr : Signal dom Bool) (funct7 : Signal dom (BitVec 7))
    : Signal dom Bool :=
  isALUrr &&& (funct7 === 0b0000001#7)

end Sparkle.IP.RV32.Decoder
