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

end Sparkle.IP.RV32.Pipeline
