/-
  RV32 trap PC selection — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (commit 01c7177). Selects which PC
  goes into mepc/sepc when a trap fires this cycle. This is the
  centerpiece of the recent decomposition effort because it sits at
  the crossroads of three concerns:

  1. Synchronous traps (ecall, page fault) must save the PC of the
     instruction that caused the trap (so the kernel handler can
     either retry or return-past).
  2. Asynchronous interrupts (timer, sw, ext) must save the PC of
     the next instruction that would have run, so the kernel resumes
     cleanly with no instruction lost.
  3. Async interrupts that fire when IDEX holds a stale instruction
     (e.g. the cycle after MRET commits) need special care: idex_pc
     would point into M-mode territory in that case.

  The fix landed in commit 01c7177 conditions on `idexLive`: if IDEX
  has a side-effect-bearing instruction it is treated as the canonical
  resume point; otherwise we fall back to pcReg.

  Priority (matches the loop body's mux chain):
    ifetch page fault > d-side page fault > async interrupt > sync trap

  Caller is responsible for ensuring at most one of the synchronous
  trap inputs (ecall / illegal / page fault) fires on any given cycle;
  this file does not enforce that.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure selector function -/

/--
  Select trap PC for `mepc` / `sepc`, given the trap-class signals and
  the candidate PC sources.

  Inputs:
  - `ifetchPF` : I-side page fault from PTW (the faulting instruction
                 never reached IDEX, so use `fetchPC`).
  - `dPF`      : D-side page fault from a load/store; the faulting
                 instruction's VA was latched into `dMissPC`.
  - `isAsync`  : an asynchronous interrupt is firing (timer/sw/ext,
                 M-mode or S-mode).
  - `idexLive` : the IDEX register currently holds a live, side-effect-
                 bearing instruction (regWrite / memRead / memWrite /
                 jump / branch / CSR / ecall / mret / sret / AMO /
                 M-ext / SFENCE.VMA).

  PCs:
  - `fetchPC` : current fetch-stage PC (next instruction to enter IFID).
  - `dMissPC` : PC of the instruction that took the d-side page fault.
  - `idexPc`  : PC of the instruction currently in IDEX.
  - `pcReg`   : the *next-fetch* PC (= fetchPC's logical predecessor;
                used when IDEX is squashed/NOP).

  Selection priority: ifetchPF > dPF > isAsync (then idexLive sub-
  decision) > otherwise idex_pc (sync trap caused by IDEX inst).
-/
@[inline] def trapPCPure
    (ifetchPF dPF isAsync idexLive : Bool)
    (fetchPC dMissPC idexPc pcReg : BitVec 32) : BitVec 32 :=
  if ifetchPF then fetchPC
  else if dPF then dMissPC
  else if isAsync then
    (if idexLive then idexPc else pcReg)
  else idexPc

/-! ## Spec invariants — Bool selector closed by `decide` -/

/-- I-side page fault: trapPC is the fetch PC. -/
@[simp] theorem trapPC_ifetchPF
    (dPF isAsync idexLive : Bool)
    (fetchPC dMissPC idexPc pcReg : BitVec 32) :
    trapPCPure true dPF isAsync idexLive fetchPC dMissPC idexPc pcReg
      = fetchPC := by
  rfl

/-- D-side page fault (no I-side competing): trapPC is dMissPC. -/
@[simp] theorem trapPC_dPF
    (isAsync idexLive : Bool)
    (fetchPC dMissPC idexPc pcReg : BitVec 32) :
    trapPCPure false true isAsync idexLive fetchPC dMissPC idexPc pcReg
      = dMissPC := by
  rfl

/-- Async interrupt with a live IDEX instruction: trapPC is idex_pc.
    After sret, the kernel re-executes the suppressed in-flight inst. -/
@[simp] theorem trapPC_async_live
    (fetchPC dMissPC idexPc pcReg : BitVec 32) :
    trapPCPure false false true true fetchPC dMissPC idexPc pcReg
      = idexPc := by
  rfl

/-- Async interrupt with a squashed/NOP IDEX: trapPC is pcReg.
    idex_pc may point into stale post-mret territory in this case. -/
@[simp] theorem trapPC_async_dead
    (fetchPC dMissPC idexPc pcReg : BitVec 32) :
    trapPCPure false false true false fetchPC dMissPC idexPc pcReg
      = pcReg := by
  rfl

/-- Synchronous trap from IDEX (no async, no page fault): trapPC = idex_pc.
    The `idexLive` flag is irrelevant in this branch. -/
@[simp] theorem trapPC_sync_live
    (fetchPC dMissPC idexPc pcReg : BitVec 32) :
    trapPCPure false false false true fetchPC dMissPC idexPc pcReg
      = idexPc := by
  rfl

@[simp] theorem trapPC_sync_dead
    (fetchPC dMissPC idexPc pcReg : BitVec 32) :
    trapPCPure false false false false fetchPC dMissPC idexPc pcReg
      = idexPc := by
  rfl

/-! ## Composite spec — exhaustive on the Bool inputs -/

/--
  Exhaustive truth table on the four Bool selectors. Quantified over
  arbitrary BitVec 32 PC sources.

  This is the single statement we want CI to depend on. -/
theorem trapPCPure_spec :
    ∀ (ifetchPF dPF isAsync idexLive : Bool)
      (fetchPC dMissPC idexPc pcReg : BitVec 32),
      trapPCPure ifetchPF dPF isAsync idexLive fetchPC dMissPC idexPc pcReg
        = (if ifetchPF then fetchPC
           else if dPF then dMissPC
           else if isAsync then
             (if idexLive then idexPc else pcReg)
           else idexPc) := by
  intros
  rfl

/-! ## Signal-level wrapper -/

/-- Signal-level trap PC selector (cycle-wise lift of `trapPCPure`). -/
def trapPCSignal {dom : DomainConfig}
    (ifetchPF dPF isAsync idexLive : Signal dom Bool)
    (fetchPC dMissPC idexPc pcReg : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux ifetchPF fetchPC
    (Signal.mux dPF dMissPC
      (Signal.mux isAsync (Signal.mux idexLive idexPc pcReg) idexPc))

/-- Cycle-wise equivalence between the Signal version and the pure
    selector. -/
theorem trapPCSignal_eq_pure {dom : DomainConfig}
    (ifetchPF dPF isAsync idexLive : Signal dom Bool)
    (fetchPC dMissPC idexPc pcReg : Signal dom (BitVec 32)) (t : Nat) :
    (trapPCSignal ifetchPF dPF isAsync idexLive
        fetchPC dMissPC idexPc pcReg).val t =
      trapPCPure
        (ifetchPF.val t) (dPF.val t) (isAsync.val t) (idexLive.val t)
        (fetchPC.val t) (dMissPC.val t) (idexPc.val t) (pcReg.val t) := by
  unfold trapPCSignal trapPCPure
  simp [Signal.mux]

end Sparkle.IP.RV32.Trap
