/-
  RV32 store-load forwarding — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 725..729). When a store
  was in EXWB the previous cycle and the load this cycle hits the
  same word, the loaded data must come from `prevStoreData` rather
  than the DRAM read port (which would still have the pre-store
  value because Signal.memory writes are registered).

  Spec:

      addrMatch    = prevStoreAddr[31:2] = loadAddr[31:2]
      storeLoadMatch = prevStoreEn ∧ addrMatch
      dmemRdataFwd = if storeLoadMatch then prevStoreData
                     else dmem_rdata

  Comparison is at word granularity (high 30 bits) because byte/half
  stores and loads inside the same word still need the forwarding
  — the per-byte enable masks and load-extractor handle the sub-word
  selection downstream.

  This forwarding is the key to making AMO and back-to-back
  store/load sequences work without a dedicated stall: the moment
  the store commits to DRAM (one cycle after EXWB), the load that
  immediately follows reads the just-stored value via this path.

  Reference: docs/RV32_Architecture_Status.md §2.3 fourth bullet
  ("Store-to-load forwarding under PTW: while pendingWriteEn, a
  load to the same word reads pendingWriteData, not stale DRAM").
  Note that pendingWriteEn is a separate path (AMO writeback) and
  uses pendingWriteData; this file covers the regular store path
  via prevStoreEn.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure forwarding predicates -/

/-- Word-granularity address match: high 30 bits of `prevStoreAddr`
    equal high 30 bits of `loadAddr`. -/
@[inline] def addrMatchPure (prevStoreAddr loadAddr : BitVec 32) : Bool :=
  prevStoreAddr.extractLsb' 2 30 == loadAddr.extractLsb' 2 30

/-- Store-load match: previous store committed AND addresses match. -/
@[inline] def storeLoadMatchPure
    (prevStoreEn : Bool) (prevStoreAddr loadAddr : BitVec 32) : Bool :=
  prevStoreEn && addrMatchPure prevStoreAddr loadAddr

/-- Forwarded DMEM read: prevStoreData if match fires, else fresh dmem_rdata. -/
@[inline] def dmemRdataFwdPure
    (storeLoadMatch : Bool) (prevStoreData dmem_rdata : BitVec 32) : BitVec 32 :=
  if storeLoadMatch then prevStoreData else dmem_rdata

/-! ## Spec invariants — closed by `bv_decide` / `decide` -/

/-- No previous store → no forwarding. -/
@[simp] theorem storeLoadMatch_no_store
    (prevStoreAddr loadAddr : BitVec 32) :
    storeLoadMatchPure false prevStoreAddr loadAddr = false := by
  rfl

/-- A previous store + a load to the same word → forward fires. -/
theorem storeLoadMatch_same_word
    (prevStoreAddr loadAddr : BitVec 32)
    (h : prevStoreAddr.extractLsb' 2 30 = loadAddr.extractLsb' 2 30) :
    storeLoadMatchPure true prevStoreAddr loadAddr = true := by
  unfold storeLoadMatchPure addrMatchPure
  simp [h]

/-- A previous store but to a different word → no forward. -/
theorem storeLoadMatch_diff_word
    (prevStoreAddr loadAddr : BitVec 32)
    (h : (prevStoreAddr.extractLsb' 2 30 == loadAddr.extractLsb' 2 30) = false) :
    storeLoadMatchPure true prevStoreAddr loadAddr = false := by
  unfold storeLoadMatchPure addrMatchPure
  simp [h]

/-- Address match is byte-offset agnostic: only the upper 30 bits matter.
    (Two addresses with same high-30 bits but different byte offsets
    inside the word still match — sub-word selection happens downstream.) -/
theorem addrMatch_ignores_byte_offset
    (a b : BitVec 32) :
    a.extractLsb' 2 30 = b.extractLsb' 2 30 →
    addrMatchPure a b = true := by
  unfold addrMatchPure
  intro h
  simp [h]

/-- A more aggressive form: if low two bits differ but high 30 match,
    addrMatch still fires. -/
theorem addrMatch_byte_aliasing :
    addrMatchPure 0x80000000#32 0x80000003#32 = true := by
  unfold addrMatchPure
  bv_decide

/-! ## Forwarded-value spec -/

/-- No match: pass through DMEM read. -/
@[simp] theorem dmemRdataFwd_no_match
    (prevStoreData dmem_rdata : BitVec 32) :
    dmemRdataFwdPure false prevStoreData dmem_rdata = dmem_rdata := by
  rfl

/-- Match: forward the previous store data. -/
@[simp] theorem dmemRdataFwd_match
    (prevStoreData dmem_rdata : BitVec 32) :
    dmemRdataFwdPure true prevStoreData dmem_rdata = prevStoreData := by
  rfl

/-! ## Composite specs -/

theorem storeLoadMatchPure_spec :
    ∀ (prevStoreEn : Bool) (prevStoreAddr loadAddr : BitVec 32),
      storeLoadMatchPure prevStoreEn prevStoreAddr loadAddr =
        (prevStoreEn && (prevStoreAddr.extractLsb' 2 30 == loadAddr.extractLsb' 2 30)) := by
  intros; rfl

theorem dmemRdataFwdPure_spec :
    ∀ (storeLoadMatch : Bool) (prevStoreData dmem_rdata : BitVec 32),
      dmemRdataFwdPure storeLoadMatch prevStoreData dmem_rdata =
        (if storeLoadMatch then prevStoreData else dmem_rdata) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def storeLoadMatchSignal {dom : DomainConfig}
    (prevStoreEn : Signal dom Bool)
    (prevStoreAddr loadAddr : Signal dom (BitVec 32)) : Signal dom Bool :=
  let storeAddrHi := prevStoreAddr.map (BitVec.extractLsb' 2 30 ·)
  let loadAddrHi := loadAddr.map (BitVec.extractLsb' 2 30 ·)
  prevStoreEn &&& (storeAddrHi === loadAddrHi)

def dmemRdataFwdSignal {dom : DomainConfig}
    (storeLoadMatch : Signal dom Bool)
    (prevStoreData dmem_rdata : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux storeLoadMatch prevStoreData dmem_rdata

/-! ## prevStoreAddr next-state

  The `prevStoreAddr` register latches the EX-stage store's
  effective address for one-cycle store-load forwarding. The
  source depends on whether MMU translation was used:

    useTranslatedAddr → dPhysAddr (PA from D-side TLB)
    else              → alu_result (raw VA = rs1 + imm)

  When MMU is off (satp.MODE = 0) the raw alu_result is the PA;
  when MMU is on, the TLB has produced a translated PA.
-/

@[inline] def prevStoreAddrPure
    (useTranslatedAddr : Bool) (dPhysAddr alu_result : BitVec 32) : BitVec 32 :=
  if useTranslatedAddr then dPhysAddr else alu_result

@[simp] theorem prevStoreAddr_translated
    (dPhysAddr alu_result : BitVec 32) :
    prevStoreAddrPure true dPhysAddr alu_result = dPhysAddr := rfl

@[simp] theorem prevStoreAddr_raw
    (dPhysAddr alu_result : BitVec 32) :
    prevStoreAddrPure false dPhysAddr alu_result = alu_result := rfl

theorem prevStoreAddrPure_spec
    (useTranslatedAddr : Bool) (dPhysAddr alu_result : BitVec 32) :
    prevStoreAddrPure useTranslatedAddr dPhysAddr alu_result =
      (if useTranslatedAddr then dPhysAddr else alu_result) := rfl

def prevStoreAddrSignal {dom : DomainConfig}
    (useTranslatedAddr : Signal dom Bool)
    (dPhysAddr alu_result : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux useTranslatedAddr dPhysAddr alu_result

end Sparkle.IP.RV32.Pipeline
