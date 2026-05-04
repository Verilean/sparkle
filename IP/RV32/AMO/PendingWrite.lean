/-
  RV32 AMO writeback latching — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 863..865). The AMO
  read-modify-write protocol works as follows:

    Cycle N: AMO instruction is in EXWB, reads memVal from DRAM,
             computes amoNewVal = AMO_op(memVal, rs2). The
             instruction does NOT commit its DRAM write this
             cycle — instead, it latches the new value into
             `pendingWriteData` and the address into
             `pendingWriteAddr`.

    Cycle N+1: The next instruction is in IDEX, but
               `pendingWriteEn = true` redirects the DRAM byte_we
               to the AMO writeback (via `final_byte_we |=
               pendingWriteEn`). The pipeline stalls IDEX with
               `divStall|pendingWriteEn`.

  Spec (next-state for the three pending-write registers):

    pendingWriteEnNext   = exwb_isAMOrw                  -- raw set
    pendingWriteAddrNext = if exwb_isAMOrw then exwb_physAddr
                           else pendingWriteAddr         -- hold
    pendingWriteDataNext = if exwb_isAMOrw then amoNewVal
                           else pendingWriteData         -- hold

  The "hold" semantics matter: while `pendingWriteEn=true` the
  next cycle, the IDEX is frozen, but the *register's input*
  reverts to the old value (via the hold arm). This means
  `pendingWriteEn` is effectively a one-cycle pulse — set on
  the EXWB-AMOrw cycle, then cleared (since `exwb_isAMOrw` is
  next-cycle a different instruction).

  Companion to:
    * `Reservation.lean` — LR/SC reservation tracking
    * `Compute.lean` — AMO op semantics (returns amoNewVal)
    * `Decode.lean` — opcode decoder
    * `SC.lean` — SC.W decode + dmem_we
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.AMO

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure next-state functions -/

/-- pendingWriteEn next-state: `exwb_isAMOrw` directly. -/
@[inline] def pendingWriteEnNextPure (exwb_isAMOrw : Bool) : Bool :=
  exwb_isAMOrw

/-- pendingWriteAddr next-state: latch `exwb_physAddr` on AMOrw, hold. -/
@[inline] def pendingWriteAddrNextPure
    (exwb_isAMOrw : Bool) (exwb_physAddr pendingWriteAddr : BitVec 32) : BitVec 32 :=
  if exwb_isAMOrw then exwb_physAddr else pendingWriteAddr

/-- pendingWriteData next-state: latch `amoNewVal` on AMOrw, hold. -/
@[inline] def pendingWriteDataNextPure
    (exwb_isAMOrw : Bool) (amoNewVal pendingWriteData : BitVec 32) : BitVec 32 :=
  if exwb_isAMOrw then amoNewVal else pendingWriteData

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- AMOrw at EXWB → set pendingWriteEn for next cycle. -/
@[simp] theorem pendingWriteEn_set : pendingWriteEnNextPure true = true := by rfl

/-- Non-AMOrw → clear pendingWriteEn. -/
@[simp] theorem pendingWriteEn_clear : pendingWriteEnNextPure false = false := by rfl

/-- AMOrw → latch the address. -/
@[simp] theorem pendingWriteAddr_latch
    (exwb_physAddr pendingWriteAddr : BitVec 32) :
    pendingWriteAddrNextPure true exwb_physAddr pendingWriteAddr = exwb_physAddr := by rfl

/-- Non-AMOrw → hold the address. -/
@[simp] theorem pendingWriteAddr_hold
    (exwb_physAddr pendingWriteAddr : BitVec 32) :
    pendingWriteAddrNextPure false exwb_physAddr pendingWriteAddr = pendingWriteAddr := by rfl

/-- AMOrw → latch the data (amoNewVal). -/
@[simp] theorem pendingWriteData_latch
    (amoNewVal pendingWriteData : BitVec 32) :
    pendingWriteDataNextPure true amoNewVal pendingWriteData = amoNewVal := by rfl

/-- Non-AMOrw → hold the data. -/
@[simp] theorem pendingWriteData_hold
    (amoNewVal pendingWriteData : BitVec 32) :
    pendingWriteDataNextPure false amoNewVal pendingWriteData = pendingWriteData := by rfl

/-! ## Joint capture invariant

  All three latches update on the same `exwb_isAMOrw` event. -/

/-- AMOrw → all three latches update simultaneously. -/
theorem pendingWrite_joint_latch
    (exwb_physAddr amoNewVal pendingWriteAddr pendingWriteData : BitVec 32) :
    pendingWriteEnNextPure true = true ∧
    pendingWriteAddrNextPure true exwb_physAddr pendingWriteAddr = exwb_physAddr ∧
    pendingWriteDataNextPure true amoNewVal pendingWriteData = amoNewVal := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- No AMOrw → all three latches hold (pendingWriteEn clears, others stay). -/
theorem pendingWrite_joint_hold
    (exwb_physAddr amoNewVal pendingWriteAddr pendingWriteData : BitVec 32) :
    pendingWriteEnNextPure false = false ∧
    pendingWriteAddrNextPure false exwb_physAddr pendingWriteAddr = pendingWriteAddr ∧
    pendingWriteDataNextPure false amoNewVal pendingWriteData = pendingWriteData := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ## Composite specs -/

theorem pendingWriteEnNextPure_spec (exwb_isAMOrw : Bool) :
    pendingWriteEnNextPure exwb_isAMOrw = exwb_isAMOrw := by rfl

theorem pendingWriteAddrNextPure_spec
    (exwb_isAMOrw : Bool) (exwb_physAddr pendingWriteAddr : BitVec 32) :
    pendingWriteAddrNextPure exwb_isAMOrw exwb_physAddr pendingWriteAddr =
      (if exwb_isAMOrw then exwb_physAddr else pendingWriteAddr) := by rfl

theorem pendingWriteDataNextPure_spec
    (exwb_isAMOrw : Bool) (amoNewVal pendingWriteData : BitVec 32) :
    pendingWriteDataNextPure exwb_isAMOrw amoNewVal pendingWriteData =
      (if exwb_isAMOrw then amoNewVal else pendingWriteData) := by rfl

/-! ## Signal-level wrappers -/

def pendingWriteEnNextSignal {dom : DomainConfig}
    (exwb_isAMOrw : Signal dom Bool) : Signal dom Bool :=
  exwb_isAMOrw

def pendingWriteAddrNextSignal {dom : DomainConfig}
    (exwb_isAMOrw : Signal dom Bool)
    (exwb_physAddr pendingWriteAddr : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux exwb_isAMOrw exwb_physAddr pendingWriteAddr

def pendingWriteDataNextSignal {dom : DomainConfig}
    (exwb_isAMOrw : Signal dom Bool)
    (amoNewVal pendingWriteData : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux exwb_isAMOrw amoNewVal pendingWriteData

end Sparkle.IP.RV32.AMO
