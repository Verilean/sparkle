/-
  RV32 PTW FSM next-state — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1650..1666). The PTW
  (page-table walker) is a 7-state FSM that handles a single
  Sv32 translation in coordination with DMEM read latency.

  States (3-bit):
    0 IDLE     idle, awaiting request
    1 L1_REQ   issuing PTE-1 read (one cycle to drive DMEM addr)
    2 L1_WAIT  waiting for PTE-1 (DMEM read latency = 1 cycle)
    3 L0_REQ   issuing PTE-0 read
    4 L0_WAIT  waiting for PTE-0
    5 DONE     PTE installed; release the bus
    6 FAULT    invalid PTE; raise page fault

  Transitions:

    IDLE → if ptwReq then L1_REQ else IDLE
    L1_REQ → L1_WAIT (always, 1-cycle DMEM latency)
    L1_WAIT → if invalid then FAULT
              else if leaf then DONE
              else L0_REQ           (nested page table pointer)
    L0_REQ → L0_WAIT
    L0_WAIT → if invalid then FAULT
              else if leaf then DONE
              else FAULT             (PTE-0 must be a leaf)
    DONE/FAULT/other → IDLE          (one-cycle pulse)

  The "L0_WAIT + nonleaf → FAULT" arm encodes the spec rule that
  Sv32 has at most 2 levels — a non-leaf at level 0 is malformed.

  PTE invalidity is `pte.V = 0` (bit 0 clear). Leaf-ness is
  `pte.R || pte.X` (read or execute permission set).
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.MMU.State

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure transition functions -/

/-- IDLE → L1_REQ (state 1) on `ptwReq`, else hold IDLE. -/
@[inline] def ptwNextFromIdlePure (ptwReq : Bool) : BitVec 3 :=
  if ptwReq then 1#3 else 0#3

/-- L1_WAIT → FAULT(6) / DONE(5) / L0_REQ(3) by PTE flags. -/
@[inline] def ptwNextFromL1WaitPure
    (dmemPteInvalid dmemPteIsLeaf : Bool) : BitVec 3 :=
  if dmemPteInvalid then 6#3
  else if dmemPteIsLeaf then 5#3
  else 3#3

/-- L0_WAIT → FAULT(6) / DONE(5) / FAULT(6) by PTE flags.
    The "non-leaf at L0 → FAULT" is the Sv32 spec rule. -/
@[inline] def ptwNextFromL0WaitPure
    (dmemPteInvalid dmemPteIsLeaf : Bool) : BitVec 3 :=
  if dmemPteInvalid then 6#3
  else if dmemPteIsLeaf then 5#3
  else 6#3

/-- Top-level PTW state next: dispatch by current state. -/
@[inline] def ptwStateNextPure
    (ptwState : BitVec 3) (ptwReq dmemPteInvalid dmemPteIsLeaf : Bool)
    : BitVec 3 :=
  if ptwIsIdlePure ptwState then ptwNextFromIdlePure ptwReq
  else if ptwIsL1ReqPure ptwState then 2#3   -- → L1_WAIT
  else if ptwIsL1WaitPure ptwState then ptwNextFromL1WaitPure dmemPteInvalid dmemPteIsLeaf
  else if ptwIsL0ReqPure ptwState then 4#3   -- → L0_WAIT
  else if ptwIsL0WaitPure ptwState then ptwNextFromL0WaitPure dmemPteInvalid dmemPteIsLeaf
  else 0#3                                    -- DONE/FAULT/other → IDLE

/-! ## Per-transition spec — closed by `decide` / `rfl` -/

/-- IDLE + no req → IDLE. -/
@[simp] theorem ptw_idle_no_req (dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure 0#3 false dmemPteInvalid dmemPteIsLeaf = 0#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwNextFromIdlePure
  rfl

/-- IDLE + req → L1_REQ. -/
@[simp] theorem ptw_idle_req (dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure 0#3 true dmemPteInvalid dmemPteIsLeaf = 1#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwNextFromIdlePure
  rfl

/-- L1_REQ → L1_WAIT. -/
@[simp] theorem ptw_l1req_to_l1wait
    (ptwReq dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure 1#3 ptwReq dmemPteInvalid dmemPteIsLeaf = 2#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure
  rfl

/-- L1_WAIT + invalid PTE → FAULT. -/
@[simp] theorem ptw_l1wait_invalid (ptwReq dmemPteIsLeaf : Bool) :
    ptwStateNextPure 2#3 ptwReq true dmemPteIsLeaf = 6#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwNextFromL1WaitPure
  rfl

/-- L1_WAIT + leaf PTE → DONE (megapage). -/
@[simp] theorem ptw_l1wait_leaf (ptwReq : Bool) :
    ptwStateNextPure 2#3 ptwReq false true = 5#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwNextFromL1WaitPure
  rfl

/-- L1_WAIT + pointer PTE (non-leaf, valid) → L0_REQ. -/
@[simp] theorem ptw_l1wait_pointer (ptwReq : Bool) :
    ptwStateNextPure 2#3 ptwReq false false = 3#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwNextFromL1WaitPure
  rfl

/-- L0_REQ → L0_WAIT. -/
@[simp] theorem ptw_l0req_to_l0wait
    (ptwReq dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure 3#3 ptwReq dmemPteInvalid dmemPteIsLeaf = 4#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwIsL0ReqPure
  rfl

/-- L0_WAIT + invalid → FAULT. -/
@[simp] theorem ptw_l0wait_invalid (ptwReq dmemPteIsLeaf : Bool) :
    ptwStateNextPure 4#3 ptwReq true dmemPteIsLeaf = 6#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwIsL0ReqPure ptwIsL0WaitPure ptwNextFromL0WaitPure
  rfl

/-- L0_WAIT + leaf → DONE. -/
@[simp] theorem ptw_l0wait_leaf (ptwReq : Bool) :
    ptwStateNextPure 4#3 ptwReq false true = 5#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwIsL0ReqPure ptwIsL0WaitPure ptwNextFromL0WaitPure
  rfl

/-- L0_WAIT + non-leaf → FAULT (Sv32 has at most 2 levels). -/
@[simp] theorem ptw_l0wait_nonleaf (ptwReq : Bool) :
    ptwStateNextPure 4#3 ptwReq false false = 6#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwIsL0ReqPure ptwIsL0WaitPure ptwNextFromL0WaitPure
  rfl

/-- DONE → IDLE (one-cycle pulse). -/
@[simp] theorem ptw_done_to_idle
    (ptwReq dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure 5#3 ptwReq dmemPteInvalid dmemPteIsLeaf = 0#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwIsL0ReqPure ptwIsL0WaitPure
  rfl

/-- FAULT → IDLE. -/
@[simp] theorem ptw_fault_to_idle
    (ptwReq dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure 6#3 ptwReq dmemPteInvalid dmemPteIsLeaf = 0#3 := by
  unfold ptwStateNextPure ptwIsIdlePure ptwIsL1ReqPure ptwIsL1WaitPure
    ptwIsL0ReqPure ptwIsL0WaitPure
  rfl

/-! ## Composite spec -/

theorem ptwStateNextPure_spec
    (ptwState : BitVec 3) (ptwReq dmemPteInvalid dmemPteIsLeaf : Bool) :
    ptwStateNextPure ptwState ptwReq dmemPteInvalid dmemPteIsLeaf =
      (if ptwIsIdlePure ptwState then ptwNextFromIdlePure ptwReq
       else if ptwIsL1ReqPure ptwState then 2#3
       else if ptwIsL1WaitPure ptwState then
         ptwNextFromL1WaitPure dmemPteInvalid dmemPteIsLeaf
       else if ptwIsL0ReqPure ptwState then 4#3
       else if ptwIsL0WaitPure ptwState then
         ptwNextFromL0WaitPure dmemPteInvalid dmemPteIsLeaf
       else 0#3) := by
  rfl

/-! ## Signal-level wrappers -/

def ptwNextFromIdleSignal {dom : DomainConfig}
    (ptwReq : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.mux ptwReq (Signal.pure 1#3) (Signal.pure 0#3)

def ptwNextFromL1WaitSignal {dom : DomainConfig}
    (dmemPteInvalid dmemPteIsLeaf : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.mux dmemPteInvalid (Signal.pure 6#3)
    (Signal.mux dmemPteIsLeaf (Signal.pure 5#3) (Signal.pure 3#3))

def ptwNextFromL0WaitSignal {dom : DomainConfig}
    (dmemPteInvalid dmemPteIsLeaf : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.mux dmemPteInvalid (Signal.pure 6#3)
    (Signal.mux dmemPteIsLeaf (Signal.pure 5#3) (Signal.pure 6#3))

def ptwStateNextSignal {dom : DomainConfig}
    (ptwIsIdle ptwIsL1Req ptwIsL1Wait ptwIsL0Req ptwIsL0Wait : Signal dom Bool)
    (ptwReq dmemPteInvalid dmemPteIsLeaf : Signal dom Bool)
    : Signal dom (BitVec 3) :=
  Signal.mux ptwIsIdle (ptwNextFromIdleSignal ptwReq)
    (Signal.mux ptwIsL1Req (Signal.pure 2#3)
    (Signal.mux ptwIsL1Wait (ptwNextFromL1WaitSignal dmemPteInvalid dmemPteIsLeaf)
    (Signal.mux ptwIsL0Req (Signal.pure 4#3)
    (Signal.mux ptwIsL0Wait (ptwNextFromL0WaitSignal dmemPteInvalid dmemPteIsLeaf)
      (Signal.pure 0#3)))))

end Sparkle.IP.RV32.MMU
