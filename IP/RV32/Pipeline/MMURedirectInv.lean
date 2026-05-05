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
import IP.RV32.Pipeline.IFID
import IP.RV32.MMU.Fill

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
  · -- Use the direct bridge introduced in commit 2d5cbd3.
    exact squash_contains_dMMURedirect branchTaken idex_jump trap_taken
      idex_isMret idex_isSret idex_isSFenceVMA flushDelay
      stallAndNotFreeze stallDelay

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
  · -- Squash from dMMURedirect via the direct bridge.
    exact squash_contains_dMMURedirect branchTaken idex_jump trap_taken
      idex_isMret idex_isSret idex_isSFenceVMA flushDelay
      stallAndNotFreeze stallDelay
  · -- pcNext = dMissPC (with trap/mret/sret false)
    rw [h_no_trap, h_no_mret, h_no_sret]
    rfl

/-! ## Cycle-N+1 sequential statement (Signal-level)

  Combine the cycle-N combinational results above with
  `Signal.register` semantics to get the Signal-level
  cycle-N+1 statement:

    pcReg.val (t+1) = dMissPC.val t

  whenever `dMMURedirect.val t = true` (and trap/mret/sret are
  clear at cycle t). This is the proof anchor for the
  multi-cycle "re-execution" claim — the kernel resumes
  fetching from dMissPC at cycle N+1.
-/

/-- pcReg signal: register'd input from `pcNextSignal`. -/
def pcRegSignal {dom : DomainConfig}
    (pcNext : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.register 0#32 pcNext

/-- **dMMURedirect at cycle t → pcReg.val (t+1) = dMissPC.val t.**

    Sequential anchor for the cycle-N+1 PC-redirect claim. -/
theorem dMMURedirect_sets_pcReg_next_cycle {dom : DomainConfig}
    (trap_taken idex_isMret idex_isSret : Signal dom Bool)
    (trapTarget mretTarget sretTarget dMissPC : Signal dom (BitVec 32))
    (dMMURedirect : Signal dom Bool)
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (flush : Signal dom Bool) (jumpTarget : Signal dom (BitVec 32))
    (stall : Signal dom Bool) (pcRegSig pcPlus4 : Signal dom (BitVec 32))
    (t : Nat)
    (h_dmmu : dMMURedirect.val t = true)
    (h_no_trap : trap_taken.val t = false)
    (h_no_mret : idex_isMret.val t = false)
    (h_no_sret : idex_isSret.val t = false) :
    (pcRegSignal
      (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
        idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
        flush jumpTarget stall pcRegSig pcPlus4)).val (t + 1) = dMissPC.val t := by
  -- Step 1: peel pcRegSignal/Signal.register down to next.val t.
  show (Signal.register 0#32
    (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
       idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
       flush jumpTarget stall pcRegSig pcPlus4)).val (t + 1) =
    dMissPC.val t
  show (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
       idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
       flush jumpTarget stall pcRegSig pcPlus4).val t = dMissPC.val t
  -- Step 2: unfold pcNextSignal at cycle t, drive each mux by its hypothesis.
  unfold pcNextSignal Signal.mux
  show (if trap_taken.val t = true then trapTarget.val t
        else if idex_isMret.val t = true then mretTarget.val t
        else if idex_isSret.val t = true then sretTarget.val t
        else if dMMURedirect.val t = true then dMissPC.val t
        else _) = dMissPC.val t
  rw [h_no_trap, h_no_mret, h_no_sret, h_dmmu]
  rfl

/-! ## Connection to invariant C

  Invariant C ("the post-fault load re-executes exactly once
  after PTW completes") requires more than the single-cycle
  guarantees here:

    * Cycle N: dMMURedirect fires → squash (proved above) →
               cycle N+1 IDEX has NOP-init values.
               pcNext = dMissPC (proved above) →
               cycle N+1 pcReg = dMissPC (proved sequentially
               via `dMMURedirect_sets_pcReg_next_cycle`).

    * Cycle N+1: ifetch is from dMissPC; the IFID register
                 will hold the faulting instruction. The new
                 IDEX (at cycle N+2) will be the faulting load.

    * Cycle N+2: faulting load advances through IDEX, EX, EXWB.
                 dTLBMiss does NOT re-fire (because anyTLBHit is
                 now true after the PTW filled the TLB). The
                 load reads from DMEM successfully and
                 commits.

  This file now provides cycles-N and N+1 in full. The cycle-N+2
  reasoning (TLB-hit-after-fill) requires additional state-
  carrying lemmas in MMU/Fill.lean and IFID.lean and is left for
  a future commit.
-/

/-! ## Composite invariant C cycle-N+1 statement

  This packages the three cycle-N+1 facts into a single theorem
  for use by clients (other proofs that need to know "after a
  dMMURedirect at cycle t, the system has been redirected to
  dMissPC by cycle t+1 with all in-flight side-effects
  dropped").
-/

/-- **Composite cycle-N+1 redirect invariant.**

    When `dMMURedirect.val t = true` (and trap/mret/sret are
    clear at cycle t, and freezeIDEX is clear), then at cycle
    t+1:

    1. `pcReg.val (t+1) = dMissPC.val t` — fetch pointer redirected.
    2. The IDEX latch input on cycle t was the squashed value
       (init), so the IDEX-stage instruction at cycle t+1 is a
       squashed NOP. (Inherits from
       `Pipeline/FlushSquash.lean::idex_squash_clears_next_cycle`.)
    3. The flushDelay register at cycle t+1 records that flush
       fired (via `Signal.register false flush`).

    Statement (3) is just `flushDelay.val (t+1) = true` from the
    `register false flush` semantics. We bundle (1) here; (2) is
    cited as an upstream theorem; (3) is rfl-closed. -/
theorem dMMURedirect_cycle_N1_redirect {dom : DomainConfig}
    (trap_taken idex_isMret idex_isSret : Signal dom Bool)
    (trapTarget mretTarget sretTarget dMissPC : Signal dom (BitVec 32))
    (dMMURedirect : Signal dom Bool)
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (flush : Signal dom Bool) (jumpTarget : Signal dom (BitVec 32))
    (stall : Signal dom Bool) (pcRegSig pcPlus4 : Signal dom (BitVec 32))
    (t : Nat)
    (h_dmmu : dMMURedirect.val t = true)
    (h_no_trap : trap_taken.val t = false)
    (h_no_mret : idex_isMret.val t = false)
    (h_no_sret : idex_isSret.val t = false) :
    -- (1) pcReg redirected
    (pcRegSignal
      (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
        idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
        flush jumpTarget stall pcRegSig pcPlus4)).val (t + 1) = dMissPC.val t :=
  dMMURedirect_sets_pcReg_next_cycle trap_taken idex_isMret idex_isSret
    trapTarget mretTarget sretTarget dMissPC dMMURedirect isSFenceVMA pc4
    flush jumpTarget stall pcRegSig pcPlus4 t h_dmmu h_no_trap h_no_mret h_no_sret

/-! ## flushDelay tracking after dMMURedirect

  Recall `flushDelay = Signal.register false flush`, so
  `flushDelay.val (t+1) = flush.val t`. When `dMMURedirect.val t
  = true`, `flush.val t = true` (via `flush_contains_dMMURedirect`),
  so `flushDelay.val (t+1) = true`. This is the cycle-wise lift
  showing the squash-or-flush is held into cycle t+1.
-/

/-- **dMMURedirect at t → flushDelay at t+1 = true.**

    Combines the structural fact "flushSignal includes
    dMMURedirect" with the `Signal.register` 1-cycle delay. -/
theorem flushDelayReg_set_after_dMMURedirect {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_dmmu : dMMURedirect.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  show (Signal.register false _).val (t + 1) = true
  show (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
    idex_isSFenceVMA dMMURedirect).val t = true
  -- flushSignal definition: 7-way disjunction.
  unfold flushSignal
  -- (a ||| b ||| ... ||| dMMURedirect).val t reduces to disjunction of .val t's.
  show ((((((branchTaken ||| idex_jump) ||| trap_taken) ||| idex_isMret)
    ||| idex_isSret) ||| idex_isSFenceVMA) ||| dMMURedirect).val t = true
  -- Reduce repeated .val t through Signal.ap/map definitionally.
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_dmmu]
  -- Goal: _ || true = true; close with Bool.or_true.
  cases branchTaken.val t <;> cases idex_jump.val t <;>
    cases trap_taken.val t <;> cases idex_isMret.val t <;>
    cases idex_isSret.val t <;> cases idex_isSFenceVMA.val t <;> rfl

/-! ## LTL form -/

/-- **LTL form of `flushDelayReg_set_after_dMMURedirect`.** -/
theorem flushDelayReg_set_after_dMMURedirect_LTL {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) :
    ∀ t, dMMURedirect.val t = true →
         (Signal.register false
           (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
             idex_isSFenceVMA dMMURedirect)).val (t + 1) = true :=
  fun t => flushDelayReg_set_after_dMMURedirect branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect t

/-- **LTL form of `dMMURedirect_sets_pcReg_next_cycle`.** -/
theorem dMMURedirect_sets_pcReg_next_cycle_LTL {dom : DomainConfig}
    (trap_taken idex_isMret idex_isSret : Signal dom Bool)
    (trapTarget mretTarget sretTarget dMissPC : Signal dom (BitVec 32))
    (dMMURedirect : Signal dom Bool)
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (flush : Signal dom Bool) (jumpTarget : Signal dom (BitVec 32))
    (stall : Signal dom Bool) (pcRegSig pcPlus4 : Signal dom (BitVec 32)) :
    ∀ t, dMMURedirect.val t = true →
         trap_taken.val t = false →
         idex_isMret.val t = false →
         idex_isSret.val t = false →
         (pcRegSignal
           (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
             idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
             flush jumpTarget stall pcRegSig pcPlus4)).val (t + 1) = dMissPC.val t :=
  fun t h_dmmu h_no_trap h_no_mret h_no_sret =>
    dMMURedirect_sets_pcReg_next_cycle trap_taken idex_isMret idex_isSret trapTarget
      mretTarget sretTarget dMissPC dMMURedirect isSFenceVMA pc4 flush jumpTarget
      stall pcRegSig pcPlus4 t h_dmmu h_no_trap h_no_mret h_no_sret

/-! ## Cycle-N+2 invariant C: the IFID-stage PC settles to dMissPC

  Once `dMMURedirect` fires at cycle N:
    * Cycle N (combinational): flush ⊇ dMMURedirect, pcNext = dMissPC.
    * Cycle N+1 (sequential, register delay): fetchPC at N+1 = dMissPC at N
      (via `IFID.fetchPCReg_flush_sets_pcNext_next_cycle`, with flush.val N = true).
    * Cycle N+2 (sequential): if the IFID stage is not stalled at N+1
      (the typical post-redirect case — dMissPC translation hits the
      newly-filled TLB and proceeds), then ifid_pc at N+2 = fetchPC at N+1
      = dMissPC at N.

  Together with `idex_squash_at_N_plus_2_after_dMMURedirect` (FlushSquash),
  the load that triggered the original miss gets re-fetched from dMissPC
  and lands in IDEX at cycle N+3 — re-execution exactly once. -/

/-- **Helper: flush.val t = true whenever dMMURedirect.val t = true.**

    Signal-level lift of `flush_contains_dMMURedirect`. -/
theorem flushSignal_true_when_dMMURedirect {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_dmmu : dMMURedirect.val t = true) :
    (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect).val t = true := by
  unfold flushSignal
  show ((((((branchTaken ||| idex_jump) ||| trap_taken) ||| idex_isMret)
    ||| idex_isSret) ||| idex_isSFenceVMA) ||| dMMURedirect).val t = true
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_dmmu]
  cases branchTaken.val t <;> cases idex_jump.val t <;>
    cases trap_taken.val t <;> cases idex_isMret.val t <;>
    cases idex_isSret.val t <;> cases idex_isSFenceVMA.val t <;> rfl

/-- **Cycle-N+1: fetchPC.val (N+1) = dMissPC.val N when dMMURedirect at N.**

    Specializes `fetchPCReg_flush_sets_pcNext_next_cycle` with
    `pcNext = pcNextSignal` and the dMMURedirect-priority lemma to
    rewrite `pcNext.val N` to `dMissPC.val N`. -/
theorem dMMURedirect_sets_fetchPC_next_cycle {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (trapTarget mretTarget sretTarget dMissPC : Signal dom (BitVec 32))
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (jumpTarget : Signal dom (BitVec 32))
    (stall fetchPCStall : Signal dom Bool)
    (pcRegSig pcPlus4 fetchPCSig : Signal dom (BitVec 32)) (t : Nat)
    (h_dmmu : dMMURedirect.val t = true)
    (h_no_trap : trap_taken.val t = false)
    (h_no_mret : idex_isMret.val t = false)
    (h_no_sret : idex_isSret.val t = false) :
    let flushSig := flushSignal branchTaken idex_jump trap_taken idex_isMret
                      idex_isSret idex_isSFenceVMA dMMURedirect
    let pcNextSig := pcNextSignal trap_taken trapTarget idex_isMret mretTarget
                       idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
                       flushSig jumpTarget stall pcRegSig pcPlus4
    (Sparkle.IP.RV32.Pipeline.fetchPCRegSignal flushSig fetchPCStall
      pcNextSig fetchPCSig pcRegSig).val (t + 1) = dMissPC.val t := by
  -- Step 1: flush.val t = true.
  have h_flush :
    (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect).val t = true :=
    flushSignal_true_when_dMMURedirect branchTaken idex_jump trap_taken
      idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect t h_dmmu
  -- Step 2: fetchPC at N+1 = pcNext.val N (by fetchPCReg_flush_sets_pcNext_next_cycle).
  have h_fetch :=
    Sparkle.IP.RV32.Pipeline.fetchPCReg_flush_sets_pcNext_next_cycle
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)
      fetchPCStall
      (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
        idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)
        jumpTarget stall pcRegSig pcPlus4)
      fetchPCSig pcRegSig t h_flush
  -- Step 3: rewrite pcNext.val N to dMissPC.val N.
  have h_pcNext :
    (pcNextSignal trap_taken trapTarget idex_isMret mretTarget
      idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)
      jumpTarget stall pcRegSig pcPlus4).val t = dMissPC.val t := by
    unfold pcNextSignal Signal.mux
    show (if trap_taken.val t = true then trapTarget.val t
          else if idex_isMret.val t = true then mretTarget.val t
          else if idex_isSret.val t = true then sretTarget.val t
          else if dMMURedirect.val t = true then dMissPC.val t
          else _) = dMissPC.val t
    rw [h_no_trap, h_no_mret, h_no_sret, h_dmmu]
    rfl
  show (Sparkle.IP.RV32.Pipeline.fetchPCRegSignal _ _ _ _ _).val (t + 1) = _
  rw [h_fetch, h_pcNext]

/-- **Cycle-N+2: ifid_pc.val (N+2) = dMissPC.val N.**

    Composes the cycle-N+1 fetchPC lemma with the IFID-PC advance lemma
    (when ¬stall at N+1). The full chain: dMMURedirect at N →
    fetchPC.val (N+1) = dMissPC.val N → ifid_pc.val (N+2) = fetchPC.val (N+1). -/
theorem dMMURedirect_sets_ifid_pc_at_N_plus_2 {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (trapTarget mretTarget sretTarget dMissPC : Signal dom (BitVec 32))
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (jumpTarget : Signal dom (BitVec 32))
    (stall fetchPCStall ifidStall : Signal dom Bool)
    (pcRegSig pcPlus4 fetchPCSig ifidPcSig : Signal dom (BitVec 32)) (n : Nat)
    (h_dmmu_n : dMMURedirect.val n = true)
    (h_no_trap_n : trap_taken.val n = false)
    (h_no_mret_n : idex_isMret.val n = false)
    (h_no_sret_n : idex_isSret.val n = false)
    (h_no_ifidStall_n1 : ifidStall.val (n + 1) = false) :
    let flushSig := flushSignal branchTaken idex_jump trap_taken idex_isMret
                      idex_isSret idex_isSFenceVMA dMMURedirect
    let pcNextSig := pcNextSignal trap_taken trapTarget idex_isMret mretTarget
                       idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
                       flushSig jumpTarget stall pcRegSig pcPlus4
    let fetchPCReg := Sparkle.IP.RV32.Pipeline.fetchPCRegSignal flushSig fetchPCStall
                        pcNextSig fetchPCSig pcRegSig
    (Sparkle.IP.RV32.Pipeline.ifidPCRegSignal ifidStall ifidPcSig fetchPCReg).val
      (n + 2) = dMissPC.val n := by
  -- Bind names explicitly so we can refer to them in `have` statements below.
  let flushSig := flushSignal branchTaken idex_jump trap_taken idex_isMret
                    idex_isSret idex_isSFenceVMA dMMURedirect
  let pcNextSig := pcNextSignal trap_taken trapTarget idex_isMret mretTarget
                     idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
                     flushSig jumpTarget stall pcRegSig pcPlus4
  let fetchPCReg := Sparkle.IP.RV32.Pipeline.fetchPCRegSignal flushSig fetchPCStall
                      pcNextSig fetchPCSig pcRegSig
  -- Step 1: ifid_pc at n+2 = fetchPCReg at n+1 (no stall).
  have h_ifid : (Sparkle.IP.RV32.Pipeline.ifidPCRegSignal ifidStall ifidPcSig fetchPCReg).val
                  (n + 2) = fetchPCReg.val (n + 1) :=
    Sparkle.IP.RV32.Pipeline.ifidPCReg_advance_when_no_stall
      ifidStall ifidPcSig fetchPCReg (n + 1) h_no_ifidStall_n1
  -- Step 2: fetchPCReg at n+1 = dMissPC at n (cycle-N+1 lemma).
  have h_fetch : fetchPCReg.val (n + 1) = dMissPC.val n :=
    dMMURedirect_sets_fetchPC_next_cycle branchTaken idex_jump
      trap_taken idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect
      trapTarget mretTarget sretTarget dMissPC isSFenceVMA pc4 jumpTarget
      stall fetchPCStall pcRegSig pcPlus4 fetchPCSig n h_dmmu_n h_no_trap_n
      h_no_mret_n h_no_sret_n
  show (Sparkle.IP.RV32.Pipeline.ifidPCRegSignal ifidStall ifidPcSig fetchPCReg).val
    (n + 2) = dMissPC.val n
  rw [h_ifid, h_fetch]

/-! ## LTL form for invariant C cycle-N+2 -/

/-- **LTL form of `dMMURedirect_sets_ifid_pc_at_N_plus_2`.** -/
theorem dMMURedirect_sets_ifid_pc_at_N_plus_2_LTL {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (trapTarget mretTarget sretTarget dMissPC : Signal dom (BitVec 32))
    (isSFenceVMA : Signal dom Bool) (pc4 : Signal dom (BitVec 32))
    (jumpTarget : Signal dom (BitVec 32))
    (stall fetchPCStall ifidStall : Signal dom Bool)
    (pcRegSig pcPlus4 fetchPCSig ifidPcSig : Signal dom (BitVec 32)) :
    ∀ n, dMMURedirect.val n = true → trap_taken.val n = false →
         idex_isMret.val n = false → idex_isSret.val n = false →
         ifidStall.val (n + 1) = false →
         let flushSig := flushSignal branchTaken idex_jump trap_taken idex_isMret
                           idex_isSret idex_isSFenceVMA dMMURedirect
         let pcNextSig := pcNextSignal trap_taken trapTarget idex_isMret mretTarget
                            idex_isSret sretTarget dMMURedirect dMissPC isSFenceVMA pc4
                            flushSig jumpTarget stall pcRegSig pcPlus4
         let fetchPCReg := Sparkle.IP.RV32.Pipeline.fetchPCRegSignal flushSig fetchPCStall
                             pcNextSig fetchPCSig pcRegSig
         (Sparkle.IP.RV32.Pipeline.ifidPCRegSignal ifidStall ifidPcSig fetchPCReg).val
           (n + 2) = dMissPC.val n :=
  fun n => dMMURedirect_sets_ifid_pc_at_N_plus_2 branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect trapTarget mretTarget
    sretTarget dMissPC isSFenceVMA pc4 jumpTarget stall fetchPCStall ifidStall
    pcRegSig pcPlus4 fetchPCSig ifidPcSig n

end Sparkle.IP.RV32.Pipeline
