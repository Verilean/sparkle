/-
  RV32 trap-entry payloads — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean`:
    * `trap_target` (line 1079) — selects S-mode or M-mode tvec base
    * `trapVal`     (line 1502) — value latched into mtval/stval

  Per RISC-V priv spec Vol II §3.1.7 (mtvec) / §4.1.5 (stvec):
  the low two bits of `mtvec`/`stvec` encode the trap-vector mode
  (00 = direct, 01 = vectored). In direct mode (which is what our
  hardware uses), every trap jumps to `tvec[31:2] ‖ 00`. We
  implement this by masking the bottom two bits with 0xFFFFFFFC.

  Per RISC-V priv spec §3.1.16 (mtval) / §4.1.10 (stval):
  the trap-value CSR receives:
    * For instruction page fault: the faulting fetch PC
    * For data page fault       : the faulting effective virtual addr
    * For other traps           : 0 (unused / cleared)
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure trap-target -/

/-- Masks the low two bits of `tvec` to 0 (direct-mode alignment). -/
@[inline] def tvecBasePure (tvec : BitVec 32) : BitVec 32 :=
  tvec &&& 0xFFFFFFFC#32

/-- 2-way trap target select: stvec (when delegated to S) vs mtvec. -/
@[inline] def trapTargetPure
    (trapToS : Bool) (mtvec stvec : BitVec 32) : BitVec 32 :=
  if trapToS then tvecBasePure stvec
  else tvecBasePure mtvec

/-! ## Pure trapVal -/

/-- 3-way trapVal select per spec:
      * ifetch page fault → fetchPC
      * d-side page fault → dMissVaddr
      * else              → 0 -/
@[inline] def trapValPure
    (ifetchPF pageFault : Bool) (fetchPC dMissVaddr : BitVec 32) : BitVec 32 :=
  if ifetchPF then fetchPC
  else if pageFault then dMissVaddr
  else 0#32

/-! ## Spec invariants — `bv_decide` for alignment, `decide`/`rfl` for selectors -/

/-- tvec base always has bits 0..1 cleared (4-byte aligned). -/
theorem tvecBase_aligned (tvec : BitVec 32) :
    (tvecBasePure tvec).extractLsb' 0 2 = 0#2 := by
  unfold tvecBasePure
  bv_decide

/-- tvec base preserves bits 31..2. -/
theorem tvecBase_high_preserved (tvec : BitVec 32) :
    (tvecBasePure tvec).extractLsb' 2 30 = tvec.extractLsb' 2 30 := by
  unfold tvecBasePure
  bv_decide

/-- M-mode trap goes to mtvec base when not delegated. -/
@[simp] theorem trapTarget_M (mtvec stvec : BitVec 32) :
    trapTargetPure false mtvec stvec = tvecBasePure mtvec := by
  rfl

/-- S-mode trap goes to stvec base when delegated. -/
@[simp] theorem trapTarget_S (mtvec stvec : BitVec 32) :
    trapTargetPure true mtvec stvec = tvecBasePure stvec := by
  rfl

/-- Trap target is always 4-byte aligned. -/
theorem trapTarget_aligned (trapToS : Bool) (mtvec stvec : BitVec 32) :
    (trapTargetPure trapToS mtvec stvec).extractLsb' 0 2 = 0#2 := by
  unfold trapTargetPure
  cases trapToS <;> simp [tvecBase_aligned]

/-! ### trapVal spec -/

/-- ifetch page fault sets trapVal to fetchPC. -/
@[simp] theorem trapVal_ifetchPF
    (pageFault : Bool) (fetchPC dMissVaddr : BitVec 32) :
    trapValPure true pageFault fetchPC dMissVaddr = fetchPC := by
  rfl

/-- d-side page fault sets trapVal to dMissVaddr (when no ifetchPF). -/
@[simp] theorem trapVal_pageFault
    (fetchPC dMissVaddr : BitVec 32) :
    trapValPure false true fetchPC dMissVaddr = dMissVaddr := by
  rfl

/-- No page fault: trapVal is 0 (unused). -/
@[simp] theorem trapVal_no_fault
    (fetchPC dMissVaddr : BitVec 32) :
    trapValPure false false fetchPC dMissVaddr = 0#32 := by
  rfl

/-! ## Composite specs -/

theorem trapTargetPure_spec :
    ∀ (trapToS : Bool) (mtvec stvec : BitVec 32),
      trapTargetPure trapToS mtvec stvec =
        (if trapToS then tvecBasePure stvec else tvecBasePure mtvec) := by
  intros; rfl

theorem trapValPure_spec :
    ∀ (ifetchPF pageFault : Bool) (fetchPC dMissVaddr : BitVec 32),
      trapValPure ifetchPF pageFault fetchPC dMissVaddr =
        (if ifetchPF then fetchPC
         else if pageFault then dMissVaddr
         else 0#32) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def tvecBaseSignal {dom : DomainConfig}
    (tvec : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mask : Signal dom (BitVec 32) := Signal.pure 0xFFFFFFFC#32
  tvec &&& mask

def trapTargetSignal {dom : DomainConfig}
    (trapToS : Signal dom Bool)
    (mtvec stvec : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux trapToS (tvecBaseSignal stvec) (tvecBaseSignal mtvec)

def trapValSignal {dom : DomainConfig}
    (ifetchPF pageFault : Signal dom Bool)
    (fetchPC dMissVaddr : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux ifetchPF fetchPC
    (Signal.mux pageFault dMissVaddr (Signal.pure 0#32))

end Sparkle.IP.RV32.Trap
