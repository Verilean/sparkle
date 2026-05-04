/-
  RV32 IF-stage instruction-source selection — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 1266..1281). The IF
  stage has two instruction sources:

    * **IMEM (firmware ROM)** at low addresses (e.g., bootloader at
      0x10000 or so).
    * **DRAM** at addresses with `bit 31 = 1` (i.e., ≥ 0x8000_0000),
      where the kernel is loaded.

  After Sv32 paging is enabled, the IF stage may translate
  `fetchPC → ifetchPhysAddr` via the iTLB. Whether the resulting
  address falls in the DRAM range is what selects the source — and
  pre-translation, the same predicate applies to `fetchPC` itself.

  This file captures three pure functions:

    1. `ifetchWordAddrPure` — bit-slice the translated/raw address
       to a 23-bit DRAM word index (assuming DRAM is 32 MB / 8M
       words).
    2. `fetchInDRAMPure` — bit-31 of the translated/raw address.
    3. `finalImemRdataPure` — 2-way mux: DRAM word vs IMEM word.

  Spec invariants:
    * `fetchInDRAMPure` is bit-31 of whichever address is selected.
    * `finalImemRdataPure` reduces to the two basic cases by `rfl`.

  Reference: `docs/RV32_Architecture_Status.md` §1.1 (memory map).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure address selection -/

/-- 23-bit DRAM word address: select from `ifetchPhysAddr` (translated) or
    `fetchPC` (raw), then take bits [24:2]. -/
@[inline] def ifetchWordAddrPure
    (ifetchTranslated : Bool) (ifetchPhysAddr fetchPC : BitVec 32) : BitVec 23 :=
  if ifetchTranslated then
    ifetchPhysAddr.extractLsb' 2 23
  else
    fetchPC.extractLsb' 2 23

/-- DRAM-vs-IMEM predicate: bit 31 of the active address. -/
@[inline] def fetchInDRAMPure
    (ifetchTranslated : Bool) (ifetchPhysAddr fetchPC : BitVec 32) : Bool :=
  if ifetchTranslated then
    ifetchPhysAddr.extractLsb' 31 1 == 1#1
  else
    fetchPC.extractLsb' 31 1 == 1#1

/-- Final IF-stage instruction word: DRAM if `fetchInDRAM`, else IMEM. -/
@[inline] def finalImemRdataPure
    (fetchInDRAM : Bool) (dramWord imemWord : BitVec 32) : BitVec 32 :=
  if fetchInDRAM then dramWord else imemWord

/-! ## Spec invariants — closed by `rfl` -/

@[simp] theorem ifetchWordAddr_translated
    (ifetchPhysAddr fetchPC : BitVec 32) :
    ifetchWordAddrPure true ifetchPhysAddr fetchPC =
      ifetchPhysAddr.extractLsb' 2 23 := by rfl

@[simp] theorem ifetchWordAddr_raw
    (ifetchPhysAddr fetchPC : BitVec 32) :
    ifetchWordAddrPure false ifetchPhysAddr fetchPC =
      fetchPC.extractLsb' 2 23 := by rfl

@[simp] theorem fetchInDRAM_translated
    (ifetchPhysAddr fetchPC : BitVec 32) :
    fetchInDRAMPure true ifetchPhysAddr fetchPC =
      (ifetchPhysAddr.extractLsb' 31 1 == 1#1) := by rfl

@[simp] theorem fetchInDRAM_raw
    (ifetchPhysAddr fetchPC : BitVec 32) :
    fetchInDRAMPure false ifetchPhysAddr fetchPC =
      (fetchPC.extractLsb' 31 1 == 1#1) := by rfl

@[simp] theorem finalImemRdata_dram
    (dramWord imemWord : BitVec 32) :
    finalImemRdataPure true dramWord imemWord = dramWord := by rfl

@[simp] theorem finalImemRdata_imem
    (dramWord imemWord : BitVec 32) :
    finalImemRdataPure false dramWord imemWord = imemWord := by rfl

/-! ## Bit-level invariants — closed by `bv_decide` -/

/-- DRAM word address takes the right slice of the translated address. -/
theorem ifetchWordAddr_translated_slice (ifetchPhysAddr fetchPC : BitVec 32) :
    (ifetchWordAddrPure true ifetchPhysAddr fetchPC) =
      ifetchPhysAddr.extractLsb' 2 23 := by rfl

/-- `fetchInDRAM` is exactly `bit31` of the active address (raw branch). -/
theorem fetchInDRAM_raw_bit31 (fetchPC : BitVec 32) :
    fetchInDRAMPure false 0#32 fetchPC =
      (fetchPC.extractLsb' 31 1 == 1#1) := by rfl

/-! ## Composite spec -/

theorem finalImemRdataPure_spec :
    ∀ (fetchInDRAM : Bool) (dramWord imemWord : BitVec 32),
      finalImemRdataPure fetchInDRAM dramWord imemWord =
        (if fetchInDRAM then dramWord else imemWord) := by
  intros; rfl

/-! ## Signal-level wrappers -/

def ifetchWordAddrSignal {dom : DomainConfig}
    (ifetchTranslated : Signal dom Bool)
    (ifetchPhysAddr fetchPC : Signal dom (BitVec 32)) : Signal dom (BitVec 23) :=
  Signal.mux ifetchTranslated
    (ifetchPhysAddr.map (BitVec.extractLsb' 2 23 ·))
    (fetchPC.map (BitVec.extractLsb' 2 23 ·))

def fetchInDRAMSignal {dom : DomainConfig}
    (ifetchTranslated : Signal dom Bool)
    (ifetchPhysAddr fetchPC : Signal dom (BitVec 32)) : Signal dom Bool :=
  Signal.mux ifetchTranslated
    ((ifetchPhysAddr.map (BitVec.extractLsb' 31 1 ·)) === 1#1)
    ((fetchPC.map (BitVec.extractLsb' 31 1 ·)) === 1#1)

def finalImemRdataSignal {dom : DomainConfig}
    (fetchInDRAM : Signal dom Bool)
    (dramWord imemWord : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  Signal.mux fetchInDRAM dramWord imemWord

end Sparkle.IP.RV32.Pipeline
