/-
  RV32 immediate decoder — pure logic + invariants

  Extracted from `IP/RV32/Core.lean` (`immGenSignal`, lines
  179..247). Picks the immediate format (I/S/B/U/J) based on the
  opcode and reconstructs the 32-bit signed-extended immediate.

  RISC-V unprivileged spec §2.2 + §2.4 + §2.5:

    opcode      mnemonic     format    immediate
    ---------   ----------   ------    ---------
    0010011     OP-IMM       I         imm[11:0]   (sign-ext)
    0000011     LOAD         I         imm[11:0]   (sign-ext)
    1100111     JALR         I         imm[11:0]   (sign-ext)
    0100011     STORE        S         imm[11:0]   (sign-ext, split)
    1100011     BRANCH       B         imm[12:0]   (sign-ext, last bit 0)
    0110111     LUI          U         imm[31:12] << 12
    0010111     AUIPC        U         imm[31:12] << 12
    1101111     JAL          J         imm[20:0]   (sign-ext, last bit 0)

  The decoder uses a priority cascade (JAL > U-type > Branch >
  Store > I-type) — for any non-matching opcode, the I-type
  extractor runs (which is the right default for OP-IMM/LOAD/JALR
  + a no-op for unknown encodings).

  Companion theorem `immGenSignal_eq_pure` proves the Signal-level
  decoder in `Core.lean` matches this pure spec cycle-by-cycle.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core
import IP.RV32.Types

namespace Sparkle.IP.RV32.Decoder

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32 (extractImmI extractImmS extractImmB extractImmU extractImmJ)

/-! ## Pure immediate decoder

  The Signal-level form constructs the immediate inline rather than
  using `extractImm*` from `Types.lean`. We provide BOTH:

    * `immGenPure` mirrors the inline construction (rfl-friendly)
    * `immGenSpecPure` is the spec form using `extractImm*`

  Then prove they're equivalent. -/

/-- Pure immediate decoder. Mirrors the inline construction in
    `Core.lean`'s `immGenSignal`. -/
@[inline] def immGenPure (opcode : BitVec 7) (inst : BitVec 32) : BitVec 32 :=
  let inst31 := inst.extractLsb' 31 1
  let signExt20 : BitVec 20 := if inst31 = 1#1 then 0xFFFFF#20 else 0#20
  let signExt19 : BitVec 19 := if inst31 = 1#1 then 0x7FFFF#19 else 0#19
  let signExt11 : BitVec 11 := if inst31 = 1#1 then 0x7FF#11 else 0#11
  -- I-type: {sign_ext[31:20], inst[31:20]}
  let immI := signExt20 ++ inst.extractLsb' 20 12
  -- S-type: {sign_ext, inst[31:25], inst[11:7]}
  let immS_a : BitVec 27 := signExt20 ++ inst.extractLsb' 25 7
  let immS := immS_a ++ inst.extractLsb' 7 5
  -- B-type: complex re-arrangement
  let immB_b31 := inst.extractLsb' 31 1
  let immB_b7  := inst.extractLsb' 7 1
  let immB_mid := inst.extractLsb' 25 6
  let immB_lo  := inst.extractLsb' 8 4
  let immB_a : BitVec 20 := signExt19 ++ immB_b31
  let immB_b : BitVec 7  := immB_b7 ++ immB_mid
  let immB_c : BitVec 5  := immB_lo ++ (0#1)
  let immB_ab : BitVec 27 := immB_a ++ immB_b
  let immB := immB_ab ++ immB_c
  -- U-type: {inst[31:12], 12'b0}
  let immU := inst.extractLsb' 12 20 ++ (0#12 : BitVec 12)
  -- J-type: {sign_ext, inst[31], inst[19:12], inst[20], inst[30:21], 0}
  let immJ_b31   := inst.extractLsb' 31 1
  let immJ_19_12 := inst.extractLsb' 12 8
  let immJ_b20   := inst.extractLsb' 20 1
  let immJ_30_21 := inst.extractLsb' 21 10
  let immJ_a : BitVec 12 := signExt11 ++ immJ_b31
  let immJ_b : BitVec 9  := immJ_19_12 ++ immJ_b20
  let immJ_c : BitVec 11 := immJ_30_21 ++ (0#1)
  let immJ_ab : BitVec 21 := immJ_a ++ immJ_b
  let immJ := immJ_ab ++ immJ_c
  -- Priority mux: JAL > U-type > Branch > Store > I-type
  let isStore  := opcode == 0b0100011#7
  let isBranch := opcode == 0b1100011#7
  let isLUI    := opcode == 0b0110111#7
  let isAUIPC  := opcode == 0b0010111#7
  let isUType  := isLUI || isAUIPC
  let isJAL    := opcode == 0b1101111#7
  if isJAL then immJ
  else if isUType then immU
  else if isBranch then immB
  else if isStore then immS
  else immI

/-! ## Per-format spec — closed by `bv_decide` -/

/-- I-type opcode (e.g. ADDI=0x13) returns the I-type spec immediate. -/
theorem immGen_I_OPIMM (inst : BitVec 32) :
    immGenPure 0b0010011#7 inst = extractImmI inst := by
  unfold immGenPure extractImmI
  bv_decide

/-- LOAD opcode returns the I-type spec immediate. -/
theorem immGen_I_LOAD (inst : BitVec 32) :
    immGenPure 0b0000011#7 inst = extractImmI inst := by
  unfold immGenPure extractImmI
  bv_decide

/-- JALR opcode returns the I-type spec immediate. -/
theorem immGen_I_JALR (inst : BitVec 32) :
    immGenPure 0b1100111#7 inst = extractImmI inst := by
  unfold immGenPure extractImmI
  bv_decide

/-- STORE opcode returns the S-type spec immediate. -/
theorem immGen_S_STORE (inst : BitVec 32) :
    immGenPure 0b0100011#7 inst = extractImmS inst := by
  unfold immGenPure extractImmS
  bv_decide

/-- BRANCH opcode returns the B-type spec immediate. -/
theorem immGen_B_BRANCH (inst : BitVec 32) :
    immGenPure 0b1100011#7 inst = extractImmB inst := by
  unfold immGenPure extractImmB
  bv_decide

/-- LUI opcode returns the U-type spec immediate. -/
theorem immGen_U_LUI (inst : BitVec 32) :
    immGenPure 0b0110111#7 inst = extractImmU inst := by
  unfold immGenPure extractImmU
  bv_decide

/-- AUIPC opcode returns the U-type spec immediate. -/
theorem immGen_U_AUIPC (inst : BitVec 32) :
    immGenPure 0b0010111#7 inst = extractImmU inst := by
  unfold immGenPure extractImmU
  bv_decide

/-- JAL opcode returns the J-type spec immediate. -/
theorem immGen_J_JAL (inst : BitVec 32) :
    immGenPure 0b1101111#7 inst = extractImmJ inst := by
  unfold immGenPure extractImmJ
  bv_decide

end Sparkle.IP.RV32.Decoder
