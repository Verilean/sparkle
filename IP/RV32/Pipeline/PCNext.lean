/-
  RV32 PC redirect — pure jumpTarget + pcNext selectors

  Extracted from `IP/RV32/SoC.lean`:
    * `jumpTarget` (lines 859..862) — branch vs JALR target
    * `pcNext`     (line 1645)      — 7-way priority redirect mux

  Spec captured:

    jumpTarget = if isJalr then (rs1 + imm) & ~1 else pc + imm

  The `& ~1` (mask out bit 0) is per RISC-V spec for JALR (sec
  §2.5.1, "the LSB of the result is set to zero"). For branches,
  the target is `pc + imm` directly (imm is already a 13-bit
  signed offset, sign-extended to 32 bits, with bit 0 = 0 by
  encoding).

  pcNext priority (high-to-low):

    trap_taken   → trap_target  (mtvec/stvec)
    isMret       → mret_target  (mepc)
    isSret       → sret_target  (sepc)
    dMMURedirect → dMissPC      (re-execute faulting load)
    isSFenceVMA  → idex_pc4     (advance after sfence)
    flush        → jumpTarget   (branch/JALR)
    stall        → pcReg        (hold)
    else         → pcPlus4      (sequential advance)
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure jump-target -/

/-- Jump target: branch (pc + imm) or JALR ((rs1 + imm) & ~1). -/
@[inline] def jumpTargetPure
    (isJalr : Bool) (pc rs1 imm : BitVec 32) : BitVec 32 :=
  if isJalr then (rs1 + imm) &&& 0xFFFFFFFE#32
  else pc + imm

/-- JALR target's LSB is always 0 (alignment guarantee). -/
theorem jumpTarget_jalr_lsb_zero (pc rs1 imm : BitVec 32) :
    (jumpTargetPure true pc rs1 imm).extractLsb' 0 1 = 0#1 := by
  unfold jumpTargetPure
  bv_decide

/-- For branch, the target is exactly pc + imm. -/
@[simp] theorem jumpTarget_branch (pc rs1 imm : BitVec 32) :
    jumpTargetPure false pc rs1 imm = pc + imm := by
  rfl

/-- For JALR, the target is `(rs1 + imm) & ~1`. -/
@[simp] theorem jumpTarget_jalr (pc rs1 imm : BitVec 32) :
    jumpTargetPure true pc rs1 imm = (rs1 + imm) &&& 0xFFFFFFFE#32 := by
  rfl

/-! ## Pure pcNext priority mux -/

/-- 8-way priority mux for the next-cycle program counter.

    Inputs:
      * `trapTaken`, `trapTarget`         — async/sync trap fires this cycle
      * `isMret`,    `mretTarget`          — mret returns to mepc
      * `isSret`,    `sretTarget`          — sret returns to sepc
      * `dMMURedirect`, `dMissPC`          — re-execute the faulting load
      * `isSFenceVMA`, `pc4`               — advance after sfence
      * `flush`,     `jumpTarget`          — branch / JALR redirect
      * `stall`,     `pcReg`               — hold during load-use stall
      * `pcPlus4`                          — sequential advance (default)
-/
@[inline] def pcNextPure
    (trapTaken : Bool) (trapTarget : BitVec 32)
    (isMret : Bool) (mretTarget : BitVec 32)
    (isSret : Bool) (sretTarget : BitVec 32)
    (dMMURedirect : Bool) (dMissPC : BitVec 32)
    (isSFenceVMA : Bool) (pc4 : BitVec 32)
    (flush : Bool) (jumpTarget : BitVec 32)
    (stall : Bool) (pcReg : BitVec 32)
    (pcPlus4 : BitVec 32) : BitVec 32 :=
  if trapTaken then trapTarget
  else if isMret then mretTarget
  else if isSret then sretTarget
  else if dMMURedirect then dMissPC
  else if isSFenceVMA then pc4
  else if flush then jumpTarget
  else if stall then pcReg
  else pcPlus4

/-! ### Priority spec — closed by `decide` over Bool -/

/-- Trap takes top priority. -/
@[simp] theorem pcNext_trap_priority
    (trapTarget : BitVec 32) (isMret : Bool) (mretTarget : BitVec 32)
    (isSret : Bool) (sretTarget : BitVec 32)
    (dMMURedirect : Bool) (dMissPC : BitVec 32)
    (isSFenceVMA : Bool) (pc4 : BitVec 32)
    (flush : Bool) (jumpTarget : BitVec 32)
    (stall : Bool) (pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      true trapTarget
      isMret mretTarget isSret sretTarget
      dMMURedirect dMissPC isSFenceVMA pc4
      flush jumpTarget stall pcReg pcPlus4 = trapTarget := by
  rfl

/-- MRET takes priority over SRET / dMMURedirect / sfence / flush / stall. -/
@[simp] theorem pcNext_mret_priority
    (trapTarget mretTarget : BitVec 32)
    (isSret : Bool) (sretTarget : BitVec 32)
    (dMMURedirect : Bool) (dMissPC : BitVec 32)
    (isSFenceVMA : Bool) (pc4 : BitVec 32)
    (flush : Bool) (jumpTarget : BitVec 32)
    (stall : Bool) (pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      false trapTarget
      true mretTarget isSret sretTarget
      dMMURedirect dMissPC isSFenceVMA pc4
      flush jumpTarget stall pcReg pcPlus4 = mretTarget := by
  rfl

/-- SRET takes priority over dMMURedirect / sfence / flush / stall. -/
@[simp] theorem pcNext_sret_priority
    (trapTarget mretTarget sretTarget : BitVec 32)
    (dMMURedirect : Bool) (dMissPC : BitVec 32)
    (isSFenceVMA : Bool) (pc4 : BitVec 32)
    (flush : Bool) (jumpTarget : BitVec 32)
    (stall : Bool) (pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      false trapTarget
      false mretTarget true sretTarget
      dMMURedirect dMissPC isSFenceVMA pc4
      flush jumpTarget stall pcReg pcPlus4 = sretTarget := by
  rfl

/-- dMMURedirect takes priority over sfence / flush / stall. -/
@[simp] theorem pcNext_dMMU_priority
    (trapTarget mretTarget sretTarget dMissPC : BitVec 32)
    (isSFenceVMA : Bool) (pc4 : BitVec 32)
    (flush : Bool) (jumpTarget : BitVec 32)
    (stall : Bool) (pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      false trapTarget
      false mretTarget false sretTarget
      true dMissPC isSFenceVMA pc4
      flush jumpTarget stall pcReg pcPlus4 = dMissPC := by
  rfl

/-- The default-arm: no event, no stall → sequential advance. -/
@[simp] theorem pcNext_default_advance
    (trapTarget mretTarget sretTarget dMissPC pc4 jumpTarget pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      false trapTarget
      false mretTarget false sretTarget
      false dMissPC false pc4
      false jumpTarget false pcReg pcPlus4 = pcPlus4 := by
  rfl

/-- Stall holds the current PC. -/
@[simp] theorem pcNext_stall_holds
    (trapTarget mretTarget sretTarget dMissPC pc4 jumpTarget pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      false trapTarget
      false mretTarget false sretTarget
      false dMissPC false pc4
      false jumpTarget true pcReg pcPlus4 = pcReg := by
  rfl

/-! ## Signal-level wrappers -/

def jumpTargetSignal {dom : DomainConfig}
    (isJalr : Signal dom Bool)
    (pc rs1 imm : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let brTarget := pc + imm
  let jalrSum := rs1 + imm
  let mask : Signal dom (BitVec 32) := Signal.pure 0xFFFFFFFE#32
  let jalrTarget := jalrSum &&& mask
  Signal.mux isJalr jalrTarget brTarget

def pcNextSignal {dom : DomainConfig}
    (trapTaken : Signal dom Bool) (trapTarget : Signal dom (BitVec 32))
    (isMret : Signal dom Bool) (mretTarget : Signal dom (BitVec 32))
    (isSret : Signal dom Bool) (sretTarget : Signal dom (BitVec 32))
    (dMMURedirect : Signal dom Bool) (dMissPC : Signal dom (BitVec 32))
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (flush : Signal dom Bool) (jumpTarget : Signal dom (BitVec 32))
    (stall : Signal dom Bool) (pcReg : Signal dom (BitVec 32))
    (pcPlus4 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux trapTaken trapTarget
    (Signal.mux isMret mretTarget
    (Signal.mux isSret sretTarget
    (Signal.mux dMMURedirect dMissPC
    (Signal.mux isSFenceVMA pc4
    (Signal.mux flush jumpTarget
    (Signal.mux stall pcReg pcPlus4))))))

end Sparkle.IP.RV32.Pipeline
