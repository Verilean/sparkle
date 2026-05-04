/-
  RV32 dMMURedirect cycle-N+1 invariants — partial sequential proof

  Builds toward invariant C from `docs/RV32_Architecture_Status.md`
  §2.2:

      "The post-fault load that set `dMissPC` re-executes
       exactly once after PTW completes."

  This is a two-cycle property. We prove the first part here:
  the cycle-N+1 invariants when `dMMURedirect` fires at cycle N.

    1. **IDEX squashed at cycle N+1**: dMMURedirect ⊆ flush ⊆ squash,
       so the IDEX register's input becomes NOP-init at cycle N+1.
       (Inherits from `FlushSquash.lean`.)

    2. **pcReg = dMissPC at cycle N+1**: dMMURedirect has high
       priority in the `pcNext` mux (above `flush`, `stall`,
       `pcPlus4`), so pcReg's input is dMissPC at cycle N.

  The second cycle (N+2): fetchPC settles to dMissPC, the new
  IFID instruction is the faulting load, which advances into IDEX
  at cycle N+3. That part is more involved (requires reasoning
  about IFID's stall-vs-advance) and is left for a future commit.

  Companion to:
    * `Pipeline/AbortGuarantee.lean` — single-cycle abort guarantee
    * `Pipeline/FlushSquash.lean` — IDEX squash invariant B
    * `Pipeline/PCNext.lean` — PC-next priority mux
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Verification.Temporal
import IP.RV32.Pipeline.FlushSquash
import IP.RV32.Pipeline.PCNext

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Temporal

/-! ## Cycle-N+1 IDEX squash on dMMURedirect

  This follows from `flush_contains_dMMURedirect` (FlushSquash)
  + `flushOrDelay_contains_flush` + `squash_contains_flushOrDelay`. -/

/--
  **dMMURedirect → flush → flushOrDelay → squash.**

  When `dMMURedirect` fires at cycle t, the `squash` signal is
  also true at t (combinational), so the IDEX register's input
  next-state defaults to its `init` value. -/
theorem dMMURedirect_implies_squash
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA stallAndNotFreeze flushDelay stallDelay : Bool) :
    flushPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA true = true ∧
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA true flushDelay)
      stallDelay = true := by
  refine ⟨?_, ?_⟩
  · -- flush fires when dMMURedirect = true
    exact flush_contains_dMMURedirect branchTaken idex_jump trap_taken
      idex_isMret idex_isSret idex_isSFenceVMA
  · -- flushOrDelay fires (since flush fires), squash fires (since flushOrDelay)
    apply squash_contains_flushOrDelay
    apply flushOrDelay_contains_flush
    exact flush_contains_dMMURedirect branchTaken idex_jump trap_taken
      idex_isMret idex_isSret idex_isSFenceVMA

/-! ## Cycle-N+1 pcReg = dMissPC on dMMURedirect

  When dMMURedirect fires (and trap/mret/sret are clear), `pcNext`
  selects `dMissPC`. Since pcReg is a `register init pcNext`, the
  value at cycle t+1 is `dMissPC.val t`. -/

/--
  **pcNext = dMissPC when dMMURedirect fires (and earlier
  selectors are clear).** -/
theorem pcNext_eq_dMissPC_on_dMMURedirect
    (trapTarget mretTarget sretTarget dMissPC : BitVec 32)
    (isSFenceVMA : Bool) (pc4 : BitVec 32)
    (flush : Bool) (jumpTarget : BitVec 32)
    (stall : Bool) (pcReg pcPlus4 : BitVec 32) :
    pcNextPure
      false trapTarget false mretTarget false sretTarget
      true dMissPC isSFenceVMA pc4
      flush jumpTarget stall pcReg pcPlus4 = dMissPC :=
  pcNext_dMMU_priority trapTarget mretTarget sretTarget dMissPC
    isSFenceVMA pc4 flush jumpTarget stall pcReg pcPlus4

/-! ## Combined: cycle-N+1 redirect + squash

  The combined statement: when `dMMURedirect` fires at cycle N
  (and trap/mret/sret are clear), then at cycle N+1:
    - The IDEX register's input was forced to NOP-init.
    - pcNext was dMissPC (so pcReg latches dMissPC at cycle N+1).

  Both follow from the per-source priority lemmas. -/

/-- For convenience: a single statement combining both invariants
    at cycle N (combinational). The cycle-N+1 register values
    follow by `Signal.register` semantics applied to the
    inputs (proven in `Pipeline/FlushSquash.lean`'s
    `idex_squash_clears_next_cycle`). -/
theorem dMMURedirect_combinational_invariants
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA stallAndNotFreeze flushDelay stallDelay : Bool)
    (trapTarget mretTarget sretTarget dMissPC pc4 jumpTarget pcReg pcPlus4 : BitVec 32)
    (h_no_trap : trap_taken = false)
    (h_no_mret : idex_isMret = false)
    (h_no_sret : idex_isSret = false) :
    -- Squash fires
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA true flushDelay)
      stallDelay = true ∧
    -- pcNext = dMissPC
    pcNextPure
      trap_taken trapTarget idex_isMret mretTarget idex_isSret sretTarget
      true dMissPC idex_isSFenceVMA pc4
      true jumpTarget false pcReg pcPlus4 = dMissPC := by
  refine ⟨?_, ?_⟩
  · -- Squash from dMMURedirect
    apply squash_contains_flushOrDelay
    apply flushOrDelay_contains_flush
    exact flush_contains_dMMURedirect branchTaken idex_jump trap_taken
      idex_isMret idex_isSret idex_isSFenceVMA
  · -- pcNext = dMissPC (with trap/mret/sret false)
    rw [h_no_trap, h_no_mret, h_no_sret]
    rfl

/-! ## Connection to invariant C

  Invariant C ("the post-fault load re-executes exactly once
  after PTW completes") requires more than the single-cycle
  guarantees here:

    * Cycle N: dMMURedirect fires → squash (proved above) →
               cycle N+1 IDEX has NOP-init values.
               pcNext = dMissPC (proved above) →
               cycle N+1 pcReg = dMissPC.

    * Cycle N+1: ifetch is from dMissPC; the IFID register
                 will hold the faulting instruction. The new
                 IDEX (at cycle N+2) will be the faulting load.

    * Cycle N+2: faulting load advances through IDEX, EX, EXWB.
                 dTLBMiss does NOT re-fire (because anyTLBHit is
                 now true after the PTW filled the TLB). The
                 load reads from DMEM successfully and
                 commits.

  The full multi-cycle proof requires reasoning over 3 cycles
  and the state of {dTLBMiss, anyTLBHit, IDEX-NOP, fetchPC}.
  This file provides the foundational cycle-N+1 invariants;
  the cycle-N+2 / dTLB-hit guarantees require additional
  modules (TLB fill state, IFID stall behavior).
-/

end Sparkle.IP.RV32.Pipeline
