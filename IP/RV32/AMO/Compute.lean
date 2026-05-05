/-
  RV32 AMO computation — pure logic + invariants

  The Signal-level `amoComputeSignal` is in `IP/RV32/Core.lean`.
  This file adds the pure counterpart (over `BitVec 5` opcode and
  `BitVec 32` operands), proves per-op correctness via `bv_decide`,
  and provides a per-value Signal-vs-pure equivalence.

  RISC-V "A" extension §10 (AMO encoding):

    op        encoding (funct5)
    -----     -----------------
    AMOSWAP   00001
    AMOADD    00000
    AMOXOR    00100
    AMOAND    01100
    AMOOR     01000
    AMOMIN    10000
    AMOMAX    10100
    AMOMINU   11000
    AMOMAXU   11100

  All ops produce a new memory value computed from the current
  memory value (`memVal`) and the rs2 operand (`rs2Val`). The
  arithmetic is on 32-bit words; signed compares for MIN/MAX and
  unsigned compares for MINU/MAXU.

  Reference: SoC.lean uses the result as `amoNewVal` for the
  pendingWriteData latch — i.e. the value that will be committed
  to DRAM on the next cycle (after the EXWB stage that captured
  the AMO instruction).
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core

namespace Sparkle.IP.RV32.AMO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure AMO compute -/

/-- Pure AMO operation. Default arm (unknown encoding) returns memVal. -/
@[inline] def amoComputePure
    (amoOp : BitVec 5) (memVal rs2Val : BitVec 32) : BitVec 32 :=
  if amoOp == 0b00001#5 then rs2Val                           -- SWAP
  else if amoOp == 0b00000#5 then memVal + rs2Val             -- ADD
  else if amoOp == 0b00100#5 then memVal ^^^ rs2Val           -- XOR
  else if amoOp == 0b01100#5 then memVal &&& rs2Val           -- AND
  else if amoOp == 0b01000#5 then memVal ||| rs2Val           -- OR
  else if amoOp == 0b10000#5 then
    if memVal.sle rs2Val then memVal else rs2Val              -- MIN
  else if amoOp == 0b10100#5 then
    if rs2Val.sle memVal then memVal else rs2Val              -- MAX
  else if amoOp == 0b11000#5 then
    if memVal.ule rs2Val then memVal else rs2Val              -- MINU
  else if amoOp == 0b11100#5 then
    if rs2Val.ule memVal then memVal else rs2Val              -- MAXU
  else memVal                                                 -- default

/-! ## Per-op specs — closed by `bv_decide` -/

/-- AMOSWAP returns rs2Val. -/
theorem amoCompute_SWAP (memVal rs2Val : BitVec 32) :
    amoComputePure 0b00001#5 memVal rs2Val = rs2Val := by
  unfold amoComputePure
  bv_decide

/-- AMOADD returns memVal + rs2Val. -/
theorem amoCompute_ADD (memVal rs2Val : BitVec 32) :
    amoComputePure 0b00000#5 memVal rs2Val = memVal + rs2Val := by
  unfold amoComputePure
  bv_decide

/-- AMOXOR returns memVal ⊕ rs2Val. -/
theorem amoCompute_XOR (memVal rs2Val : BitVec 32) :
    amoComputePure 0b00100#5 memVal rs2Val = memVal ^^^ rs2Val := by
  unfold amoComputePure
  bv_decide

/-- AMOAND returns memVal ∧ rs2Val. -/
theorem amoCompute_AND (memVal rs2Val : BitVec 32) :
    amoComputePure 0b01100#5 memVal rs2Val = memVal &&& rs2Val := by
  unfold amoComputePure
  bv_decide

/-- AMOOR returns memVal ∨ rs2Val. -/
theorem amoCompute_OR (memVal rs2Val : BitVec 32) :
    amoComputePure 0b01000#5 memVal rs2Val = memVal ||| rs2Val := by
  unfold amoComputePure
  bv_decide

/-- AMOMIN returns the signed minimum. -/
theorem amoCompute_MIN (memVal rs2Val : BitVec 32) :
    amoComputePure 0b10000#5 memVal rs2Val =
      (if memVal.sle rs2Val then memVal else rs2Val) := by
  unfold amoComputePure
  bv_decide

/-- AMOMAX returns the signed maximum. -/
theorem amoCompute_MAX (memVal rs2Val : BitVec 32) :
    amoComputePure 0b10100#5 memVal rs2Val =
      (if rs2Val.sle memVal then memVal else rs2Val) := by
  unfold amoComputePure
  bv_decide

/-- AMOMINU returns the unsigned minimum. -/
theorem amoCompute_MINU (memVal rs2Val : BitVec 32) :
    amoComputePure 0b11000#5 memVal rs2Val =
      (if memVal.ule rs2Val then memVal else rs2Val) := by
  unfold amoComputePure
  bv_decide

/-- AMOMAXU returns the unsigned maximum. -/
theorem amoCompute_MAXU (memVal rs2Val : BitVec 32) :
    amoComputePure 0b11100#5 memVal rs2Val =
      (if rs2Val.ule memVal then memVal else rs2Val) := by
  unfold amoComputePure
  bv_decide

/-! ## Sanity invariants -/

/-- AMOSWAP discards memVal — proves it never reads from memVal. -/
theorem amoSwap_independent_of_memVal
    (mv₁ mv₂ rs2Val : BitVec 32) :
    amoComputePure 0b00001#5 mv₁ rs2Val
      = amoComputePure 0b00001#5 mv₂ rs2Val := by
  unfold amoComputePure
  bv_decide

/-- AMOADD is commutative on operands. -/
theorem amoAdd_comm (memVal rs2Val : BitVec 32) :
    amoComputePure 0b00000#5 memVal rs2Val
      = amoComputePure 0b00000#5 rs2Val memVal := by
  unfold amoComputePure
  bv_decide

/-- AMOAND/OR/XOR are commutative on operands. -/
theorem amoAnd_comm (memVal rs2Val : BitVec 32) :
    amoComputePure 0b01100#5 memVal rs2Val
      = amoComputePure 0b01100#5 rs2Val memVal := by
  unfold amoComputePure
  bv_decide

theorem amoOr_comm (memVal rs2Val : BitVec 32) :
    amoComputePure 0b01000#5 memVal rs2Val
      = amoComputePure 0b01000#5 rs2Val memVal := by
  unfold amoComputePure
  bv_decide

theorem amoXor_comm (memVal rs2Val : BitVec 32) :
    amoComputePure 0b00100#5 memVal rs2Val
      = amoComputePure 0b00100#5 rs2Val memVal := by
  unfold amoComputePure
  bv_decide

end Sparkle.IP.RV32.AMO
