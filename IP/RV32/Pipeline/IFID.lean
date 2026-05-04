/-
  RV32 IFID-stage register inputs — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 1277..1280). The IFID
  stage holds the instruction fetched from IMEM along with its
  PC and PC+4. Three register inputs (next-state computations):

    ifid_inst_in:  3-way priority
                    flush ∨ stallDelay → NOP (0x00000013 = ADDI x0, x0, 0)
                    stall              → hold ifid_inst
                    else               → new instruction from IMEM

    ifid_pc_in:    2-way
                    stall → hold ifid_pc
                    else  → fetchPC

    ifid_pc4_in:   2-way
                    stall → hold ifid_pc4
                    else  → fetchPCPlus4

  The "stallDelay → NOP" arm is the bug fix in commit ... (see
  SoC.lean's note): on the cycle after a stall releases, fetchPC
  lags pcReg, so both the stalled and post-stall fetches return
  the same IMEM word. NOP-ing IFID on the stall-release cycle
  prevents the duplicate from entering IDEX twice.

  Reference: docs/RV32_Architecture_Status.md §1.2 (pipeline
  policy: "IFID hold during load-use stall, NOP-flush on
  branch/JAL/JALR/trap").
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## NOP encoding -/

/-- NOP = `ADDI x0, x0, 0` = 0x00000013. -/
def nopInstPure : BitVec 32 := 0x00000013#32

/-! ## Pure IFID register inputs -/

/-- ifid_inst next: 3-way priority.
      flushOrDelay ∨ stallDelay → NOP
      stall                     → hold (ifid_inst)
      else                      → new (final_imem_rdata) -/
@[inline] def ifidInstNextPure
    (flushOrDelay stallDelay stall : Bool)
    (ifid_inst final_imem_rdata : BitVec 32) : BitVec 32 :=
  if flushOrDelay || stallDelay then nopInstPure
  else if stall then ifid_inst
  else final_imem_rdata

/-- ifid_pc next: stall holds, else load fetchPC. -/
@[inline] def ifidPCNextPure
    (stall : Bool) (ifid_pc fetchPC : BitVec 32) : BitVec 32 :=
  if stall then ifid_pc else fetchPC

/-- ifid_pc4 next: stall holds, else load fetchPCPlus4. -/
@[inline] def ifidPC4NextPure
    (stall : Bool) (ifid_pc4 fetchPCPlus4 : BitVec 32) : BitVec 32 :=
  if stall then ifid_pc4 else fetchPCPlus4

/-! ## Spec invariants — closed by `decide` / `rfl` -/

/-- flush wins over stall (NOPs out). -/
@[simp] theorem ifidInst_flush_to_nop
    (stallDelay stall : Bool) (ifid_inst final_imem_rdata : BitVec 32) :
    ifidInstNextPure true stallDelay stall ifid_inst final_imem_rdata
      = nopInstPure := by rfl

/-- stallDelay wins over stall (NOPs out — duplicate-instruction fix). -/
@[simp] theorem ifidInst_stallDelay_to_nop
    (stall : Bool) (ifid_inst final_imem_rdata : BitVec 32) :
    ifidInstNextPure false true stall ifid_inst final_imem_rdata
      = nopInstPure := by rfl

/-- stall (no flush, no stallDelay) holds the current ifid_inst. -/
@[simp] theorem ifidInst_stall_holds
    (ifid_inst final_imem_rdata : BitVec 32) :
    ifidInstNextPure false false true ifid_inst final_imem_rdata = ifid_inst := by rfl

/-- No event → load new from IMEM. -/
@[simp] theorem ifidInst_default_advance
    (ifid_inst final_imem_rdata : BitVec 32) :
    ifidInstNextPure false false false ifid_inst final_imem_rdata
      = final_imem_rdata := by rfl

/-! ### ifid_pc / ifid_pc4 spec -/

@[simp] theorem ifidPC_stall_holds (ifid_pc fetchPC : BitVec 32) :
    ifidPCNextPure true ifid_pc fetchPC = ifid_pc := by rfl

@[simp] theorem ifidPC_advance (ifid_pc fetchPC : BitVec 32) :
    ifidPCNextPure false ifid_pc fetchPC = fetchPC := by rfl

@[simp] theorem ifidPC4_stall_holds (ifid_pc4 fetchPCPlus4 : BitVec 32) :
    ifidPC4NextPure true ifid_pc4 fetchPCPlus4 = ifid_pc4 := by rfl

@[simp] theorem ifidPC4_advance (ifid_pc4 fetchPCPlus4 : BitVec 32) :
    ifidPC4NextPure false ifid_pc4 fetchPCPlus4 = fetchPCPlus4 := by rfl

/-! ## Composite specs -/

theorem ifidInstNextPure_spec
    (flushOrDelay stallDelay stall : Bool)
    (ifid_inst final_imem_rdata : BitVec 32) :
    ifidInstNextPure flushOrDelay stallDelay stall ifid_inst final_imem_rdata =
      (if flushOrDelay || stallDelay then nopInstPure
       else if stall then ifid_inst
       else final_imem_rdata) := by rfl

/-! ## Signal-level wrappers -/

def ifidInstNextSignal {dom : DomainConfig}
    (flushOrDelay stallDelay stall : Signal dom Bool)
    (ifid_inst final_imem_rdata : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let nopSig : Signal dom (BitVec 32) := Signal.pure nopInstPure
  Signal.mux (flushOrDelay ||| stallDelay) nopSig
    (Signal.mux stall ifid_inst final_imem_rdata)

def ifidPCNextSignal {dom : DomainConfig}
    (stall : Signal dom Bool)
    (ifid_pc fetchPC : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux stall ifid_pc fetchPC

def ifidPC4NextSignal {dom : DomainConfig}
    (stall : Signal dom Bool)
    (ifid_pc4 fetchPCPlus4 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux stall ifid_pc4 fetchPCPlus4

/-! ## fetchPC next-state

  `fetchPC` is the IF-stage instruction-fetch PC, distinct from
  `pcReg` because IF and IDEX may run on slightly different
  PCs during stall. The next-state is:

    fetchPC_next = if flush then pcNext         (redirect)
                   else if stall then fetchPC   (hold)
                   else                pcReg    (advance to pcReg)

  This is the "Bug fix #3" referenced in SoC.lean: on flush,
  fetchPC must take pcNext (not pcReg), otherwise the IF stage
  fetches from the wrong PC. -/

@[inline] def fetchPCNextPure
    (flush stall : Bool) (pcNext fetchPC pcReg : BitVec 32) : BitVec 32 :=
  if flush then pcNext
  else if stall then fetchPC
  else pcReg

@[simp] theorem fetchPCNext_flush
    (stall : Bool) (pcNext fetchPC pcReg : BitVec 32) :
    fetchPCNextPure true stall pcNext fetchPC pcReg = pcNext := by rfl

@[simp] theorem fetchPCNext_stall
    (pcNext fetchPC pcReg : BitVec 32) :
    fetchPCNextPure false true pcNext fetchPC pcReg = fetchPC := by rfl

@[simp] theorem fetchPCNext_advance
    (pcNext fetchPC pcReg : BitVec 32) :
    fetchPCNextPure false false pcNext fetchPC pcReg = pcReg := by rfl

def fetchPCNextSignal {dom : DomainConfig}
    (flush stall : Signal dom Bool)
    (pcNext fetchPC pcReg : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux flush pcNext (Signal.mux stall fetchPC pcReg)

/-! ## Sequential: flush at cycle t → fetchPC.val (t+1) = pcNext.val t

  This is the IFID-side counterpart of `pcReg`'s redirect. When
  `flush.val t = true` (any of branchTaken / idex_jump /
  trap_taken / mret / sret / sfence / dMMURedirect), the
  `fetchPC` register's input at cycle t is `pcNext.val t`, so
  the fetch PC is updated to `pcNext` at cycle t+1.

  This is the cycle-N+1 handoff for invariant C: when
  `dMMURedirect` fires at N, `flush = true` at N (since
  flush ⊇ dMMURedirect), `pcNext = dMissPC` at N, so
  fetchPC at N+1 = dMissPC.val N — the IF stage starts
  re-fetching the faulting load.
-/

/-- `fetchPC` register: input runs through `fetchPCNextSignal`. -/
def fetchPCRegSignal {dom : DomainConfig}
    (flush stall : Signal dom Bool)
    (pcNext fetchPC pcReg : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.register 0#32 (fetchPCNextSignal flush stall pcNext fetchPC pcReg)

/-- **flush at cycle t → fetchPC.val (t+1) = pcNext.val t.**

    This is the sequential handoff: a flush this cycle redirects
    fetch to `pcNext` next cycle. -/
theorem fetchPCReg_flush_sets_pcNext_next_cycle {dom : DomainConfig}
    (flush stall : Signal dom Bool)
    (pcNext fetchPC pcReg : Signal dom (BitVec 32)) (t : Nat)
    (h_flush : flush.val t = true) :
    (fetchPCRegSignal flush stall pcNext fetchPC pcReg).val (t + 1) =
      pcNext.val t := by
  unfold fetchPCRegSignal
  show (Signal.register 0#32 _).val (t + 1) = _
  -- (register 0 next).val (t+1) = next.val t
  show (fetchPCNextSignal flush stall pcNext fetchPC pcReg).val t = _
  unfold fetchPCNextSignal Signal.mux
  show (if flush.val t = true then pcNext.val t
        else if stall.val t = true then fetchPC.val t
        else pcReg.val t) = pcNext.val t
  rw [h_flush]
  rfl

end Sparkle.IP.RV32.Pipeline
