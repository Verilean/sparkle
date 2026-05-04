/-
  RV32 M-extension division — pure logic + invariants

  Mirrors the divide-related arms of `mextCompute` (`IP/RV32/Core.lean`,
  lines 415..439). The four ops are DIV, DIVU, REM, REMU.

  Per RISC-V "M" extension §7.2 (edge cases):

    DIV  by 0           → 0xFFFFFFFF (-1 in two's complement)
    DIVU by 0           → 0xFFFFFFFF
    REM  by 0           → dividend
    REMU by 0           → dividend
    DIV  INT_MIN by -1  → INT_MIN  (no exception, defined behavior)
    REM  INT_MIN by -1  → 0
    DIVU/REMU never overflow (no signed-overflow case)

  This file provides pure functions matching these spec rules, and
  per-edge-case theorems verifying the rules hold. The proofs are
  mostly `rfl` after unfolding, since the edge case is encoded
  directly via `if rs2 == 0` style.

  Reference: this is the M-extension's spec form. The hardware
  uses a multi-cycle restoring-division circuit (see the divider
  module in `IP/RV32/Divider.lean`); the equivalence between the
  two is a separate (open) verification target.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Mext

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure division ops -/

/-- Signed division (DIV). -/
@[inline] def divPure (rs1 rs2 : BitVec 32) : BitVec 32 :=
  if rs2 == 0#32 then 0xFFFFFFFF#32                              -- div by 0
  else if rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32 then
    0x80000000#32                                                 -- INT_MIN / -1
  else
    BitVec.ofInt 32 (rs1.toInt / rs2.toInt)

/-- Unsigned division (DIVU). -/
@[inline] def divuPure (rs1 rs2 : BitVec 32) : BitVec 32 :=
  if rs2 == 0#32 then 0xFFFFFFFF#32
  else BitVec.ofNat 32 (rs1.toNat / rs2.toNat)

/-- Signed remainder (REM). -/
@[inline] def remPure (rs1 rs2 : BitVec 32) : BitVec 32 :=
  if rs2 == 0#32 then rs1                                        -- rem by 0
  else if rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32 then
    0#32                                                          -- INT_MIN % -1
  else
    BitVec.ofInt 32 (rs1.toInt % rs2.toInt)

/-- Unsigned remainder (REMU). -/
@[inline] def remuPure (rs1 rs2 : BitVec 32) : BitVec 32 :=
  if rs2 == 0#32 then rs1
  else BitVec.ofNat 32 (rs1.toNat % rs2.toNat)

/-! ## Edge-case spec — closed by `rfl` after unfold -/

/-- DIV by 0 returns 0xFFFFFFFF (-1). -/
theorem div_by_zero (rs1 : BitVec 32) :
    divPure rs1 0#32 = 0xFFFFFFFF#32 := by
  unfold divPure
  rfl

/-- DIVU by 0 returns 0xFFFFFFFF. -/
theorem divu_by_zero (rs1 : BitVec 32) :
    divuPure rs1 0#32 = 0xFFFFFFFF#32 := by
  unfold divuPure
  rfl

/-- REM by 0 returns dividend. -/
theorem rem_by_zero (rs1 : BitVec 32) :
    remPure rs1 0#32 = rs1 := by
  unfold remPure
  rfl

/-- REMU by 0 returns dividend. -/
theorem remu_by_zero (rs1 : BitVec 32) :
    remuPure rs1 0#32 = rs1 := by
  unfold remuPure
  rfl

/-- DIV INT_MIN by -1 returns INT_MIN. -/
theorem div_int_min_neg_one :
    divPure 0x80000000#32 0xFFFFFFFF#32 = 0x80000000#32 := by
  unfold divPure
  rfl

/-- REM INT_MIN by -1 returns 0. -/
theorem rem_int_min_neg_one :
    remPure 0x80000000#32 0xFFFFFFFF#32 = 0#32 := by
  unfold remPure
  rfl

/-! ## Note on algebraic invariants

  Genuine algebraic invariants of division (e.g. "DIV by 1 returns
  the dividend", "DIV a 0 = -1 for all a") would follow from the
  generic `Int.ediv_one` and `Nat.div_one` theorems. Stating them
  here as `BitVec` theorems requires bridging `BitVec.toInt /
  BitVec.toInt` back through `BitVec.ofInt`, which depends on
  mathlib lemmas not always available. We focus on the edge-case
  theorems above; the sanity invariants are accessible via the
  `Int`/`Nat` versions in mathlib. -/

/-! ## Composite specs -/

theorem divPure_spec (rs1 rs2 : BitVec 32) :
    divPure rs1 rs2 =
      (if rs2 == 0#32 then 0xFFFFFFFF#32
       else if rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32 then
         0x80000000#32
       else
         BitVec.ofInt 32 (rs1.toInt / rs2.toInt)) := by rfl

theorem divuPure_spec (rs1 rs2 : BitVec 32) :
    divuPure rs1 rs2 =
      (if rs2 == 0#32 then 0xFFFFFFFF#32
       else BitVec.ofNat 32 (rs1.toNat / rs2.toNat)) := by rfl

theorem remPure_spec (rs1 rs2 : BitVec 32) :
    remPure rs1 rs2 =
      (if rs2 == 0#32 then rs1
       else if rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32 then 0#32
       else BitVec.ofInt 32 (rs1.toInt % rs2.toInt)) := by rfl

theorem remuPure_spec (rs1 rs2 : BitVec 32) :
    remuPure rs1 rs2 =
      (if rs2 == 0#32 then rs1
       else BitVec.ofNat 32 (rs1.toNat % rs2.toNat)) := by rfl

/-! ## Divider control bits

  The DIV/REM/DIVU/REMU instructions are distinguished by funct3:

    funct3 | mnemonic | signed? | rem?
    -------|----------|---------|------
    100    | DIV      | yes     | no
    101    | DIVU     | no      | no
    110    | REM      | yes     | yes
    111    | REMU     | no      | yes

  So bit 0 = "unsigned" and bit 1 = "remainder":

    divIsSigned = !funct3[0]
    divIsRem    =  funct3[1]
-/

@[inline] def divIsSignedPure (funct3 : BitVec 3) : Bool :=
  !(funct3.extractLsb' 0 1 == 1#1)

@[inline] def divIsRemPure (funct3 : BitVec 3) : Bool :=
  funct3.extractLsb' 1 1 == 1#1

/-- DIV: signed, no rem. -/
@[simp] theorem divIsSigned_DIV : divIsSignedPure 0b100#3 = true := by
  unfold divIsSignedPure; rfl
@[simp] theorem divIsRem_DIV : divIsRemPure 0b100#3 = false := by
  unfold divIsRemPure; rfl

/-- DIVU: unsigned, no rem. -/
@[simp] theorem divIsSigned_DIVU : divIsSignedPure 0b101#3 = false := by
  unfold divIsSignedPure; rfl
@[simp] theorem divIsRem_DIVU : divIsRemPure 0b101#3 = false := by
  unfold divIsRemPure; rfl

/-- REM: signed, rem. -/
@[simp] theorem divIsSigned_REM : divIsSignedPure 0b110#3 = true := by
  unfold divIsSignedPure; rfl
@[simp] theorem divIsRem_REM : divIsRemPure 0b110#3 = true := by
  unfold divIsRemPure; rfl

/-- REMU: unsigned, rem. -/
@[simp] theorem divIsSigned_REMU : divIsSignedPure 0b111#3 = false := by
  unfold divIsSignedPure; rfl
@[simp] theorem divIsRem_REMU : divIsRemPure 0b111#3 = true := by
  unfold divIsRemPure; rfl

def divIsSignedSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  ~~~((funct3.map (BitVec.extractLsb' 0 1 ·)) === 1#1)

def divIsRemSignal {dom : DomainConfig}
    (funct3 : Signal dom (BitVec 3)) : Signal dom Bool :=
  (funct3.map (BitVec.extractLsb' 1 1 ·)) === 1#1

end Sparkle.IP.RV32.Mext
