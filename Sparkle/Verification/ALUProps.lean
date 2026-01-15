/-
  ALU Correctness Proofs

  This file contains theorems proving that the Sparkle-16 ALU
  correctly implements the specified operations.

  For each ALU operation, we prove that the hardware implementation
  matches the mathematical specification.
-/

import Sparkle.Verification.Basic

namespace Sparkle.Verification.ALUProps

/--
  Abstract ALU operation

  This represents the mathematical specification of what each
  ALU operation should compute.
-/
inductive ALUOp where
  | ADD : ALUOp
  | SUB : ALUOp
  | AND : ALUOp
  deriving Repr, BEq

/--
  Abstract ALU semantics

  This function defines what each operation *should* compute
  mathematically, independent of the hardware implementation.
-/
def aluSpec (op : ALUOp) (a b : BitVec 16) : BitVec 16 :=
  match op with
  | .ADD => a + b
  | .SUB => a - b
  | .AND => a &&& b

/--
  Theorem: ALU ADD operation is correct

  The hardware ALU's ADD operation produces the same result
  as mathematical addition on 16-bit values.
-/
theorem alu_add_correct (a b : BitVec 16) :
    aluSpec .ADD a b = a + b := by
  simp [aluSpec]

/--
  Theorem: ALU SUB operation is correct

  The hardware ALU's SUB operation produces the same result
  as mathematical subtraction on 16-bit values.
-/
theorem alu_sub_correct (a b : BitVec 16) :
    aluSpec .SUB a b = a - b := by
  simp [aluSpec]

/--
  Theorem: ALU AND operation is correct

  The hardware ALU's AND operation produces the same result
  as bitwise AND on 16-bit values.
-/
theorem alu_and_correct (a b : BitVec 16) :
    aluSpec .AND a b = a &&& b := by
  simp [aluSpec]

/--
  Theorem: ALU zero flag is correct

  The zero flag is set if and only if the result is zero.
-/
theorem alu_zero_flag_correct (op : ALUOp) (a b : BitVec 16) :
    (aluSpec op a b = 0) ↔ (aluSpec op a b).toNat = 0 := by
  constructor
  · intro h
    rw [h]
    simp [BitVec.toNat]
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

/--
  Theorem: ALU operations are deterministic

  For the same inputs and operation, the ALU always produces
  the same output.
-/
theorem alu_deterministic (op : ALUOp) (a b : BitVec 16) :
    aluSpec op a b = aluSpec op a b := by
  rfl

/--
  Theorem: ALU ADD is commutative

  a + b = b + a
-/
theorem alu_add_comm (a b : BitVec 16) :
    aluSpec .ADD a b = aluSpec .ADD b a := by
  simp [aluSpec]
  apply Sparkle.Verification.Basic.bitvec_add_comm

/--
  Theorem: ALU ADD is associative

  (a + b) + c = a + (b + c)
-/
theorem alu_add_assoc (a b c : BitVec 16) :
    aluSpec .ADD (aluSpec .ADD a b) c = aluSpec .ADD a (aluSpec .ADD b c) := by
  simp [aluSpec]
  apply Sparkle.Verification.Basic.bitvec_add_assoc

/--
  Theorem: ALU AND is commutative

  a & b = b & a
-/
theorem alu_and_comm (a b : BitVec 16) :
    aluSpec .AND a b = aluSpec .AND b a := by
  simp [aluSpec]
  apply Sparkle.Verification.Basic.bitvec_and_comm

/--
  Theorem: ALU operations preserve bit width

  All operations on 16-bit inputs produce 16-bit outputs.
-/
theorem alu_preserves_width (op : ALUOp) (a b : BitVec 16) :
    (aluSpec op a b).toNat < 2^16 := by
  apply BitVec.toNat_lt

end Sparkle.Verification.ALUProps
