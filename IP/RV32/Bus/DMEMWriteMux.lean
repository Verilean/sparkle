/-
  RV32 DMEM-write 2-stage priority mux — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 629..650). The DRAM
  write port has two priority overrides:

    1. **Pending AMO writeback** — when an AMO instruction's
       read-modify-write protocol latched a value to commit on
       the next cycle, that write takes priority over the EX
       stage's own store. (`pendingWriteEn` is set in cycle
       N for AMOrw committed at cycle N-1.)

    2. **External write** — when firmware-loader machinery
       drives `dmemExtWriteEn`, that takes priority over both
       the AMO writeback and the EX-stage store. Used during
       cold boot to populate the kernel image into DRAM before
       the CPU starts fetching.

  Final priority: external > pending-AMO > EX-stage.

  This file captures both stages as pure functions and proves
  the priority + byte-enable rules:

    finalAddr  = if pendingWE then pendWordAddr else dmemAddr
    finalByteI = if pendingWE then pendByteI    else byteIWdata
    finalByteI_we = byteI_we ∨ pendingWE         -- AMO sets all 4 lanes

    actualAddr  = if extWE  then extWriteAddr   else finalAddr
    actualByteI = if extWE  then extByteI       else finalByteI
    protoByteI_we = finalByteI_we ∨ extWE        -- external sets all 4

  Invariants:
    * Pending-AMO write covers all 4 byte lanes (4-byte word).
    * External write covers all 4 byte lanes.
    * If neither override is active, EX-stage's per-lane WEs
      survive unchanged.

  Reference: `Tests/RV32/JITLinuxBootTest.lean` — exercises both
  external-write (initial firmware load) and AMO writeback paths
  during Linux boot.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Stage 1: pending-AMO override -/

/-- Address mux: pendingWE → pendWordAddr; else dmemAddr. -/
@[inline] def finalDmemAddrPure
    (pendingWE : Bool) (pendWordAddr dmemAddr : BitVec 23) : BitVec 23 :=
  if pendingWE then pendWordAddr else dmemAddr

/-- Byte-data mux (per-lane): pendingWE → pendByte; else byteWdata. -/
@[inline] def finalDmemByteWdataPure
    (pendingWE : Bool) (pendByte byteWdata : BitVec 8) : BitVec 8 :=
  if pendingWE then pendByte else byteWdata

/-- Byte-WE: byteI_we OR pendingWE (AMO sets all 4 lanes). -/
@[inline] def finalDmemByteWePure
    (byteWe pendingWE : Bool) : Bool :=
  byteWe || pendingWE

/-! ## Stage 2: external-write override -/

/-- Address mux: extWE → extAddr; else finalAddr. -/
@[inline] def actualDmemAddrPure
    (extWE : Bool) (extAddr finalAddr : BitVec 23) : BitVec 23 :=
  if extWE then extAddr else finalAddr

/-- Byte-data mux (per-lane): extWE → extByte; else finalByte. -/
@[inline] def actualDmemByteWdataPure
    (extWE : Bool) (extByte finalByte : BitVec 8) : BitVec 8 :=
  if extWE then extByte else finalByte

/-- Proto byte-WE: finalWe OR extWE. -/
@[inline] def protoDmemByteWePure
    (finalWe extWE : Bool) : Bool :=
  finalWe || extWE

/-! ## Spec invariants — closed by `rfl` / `decide` -/

@[simp] theorem finalDmemAddr_amo (pendWordAddr dmemAddr : BitVec 23) :
    finalDmemAddrPure true pendWordAddr dmemAddr = pendWordAddr := rfl

@[simp] theorem finalDmemAddr_normal (pendWordAddr dmemAddr : BitVec 23) :
    finalDmemAddrPure false pendWordAddr dmemAddr = dmemAddr := rfl

@[simp] theorem finalDmemByteWdata_amo (pendByte byteWdata : BitVec 8) :
    finalDmemByteWdataPure true pendByte byteWdata = pendByte := rfl

@[simp] theorem finalDmemByteWdata_normal (pendByte byteWdata : BitVec 8) :
    finalDmemByteWdataPure false pendByte byteWdata = byteWdata := rfl

/-- AMO writeback covers all 4 byte lanes (regardless of byteWe). -/
@[simp] theorem finalDmemByteWe_amo (byteWe : Bool) :
    finalDmemByteWePure byteWe true = true := by
  unfold finalDmemByteWePure; cases byteWe <;> rfl

/-- No AMO → byteWe is unchanged. -/
@[simp] theorem finalDmemByteWe_normal (byteWe : Bool) :
    finalDmemByteWePure byteWe false = byteWe := by
  unfold finalDmemByteWePure; cases byteWe <;> rfl

@[simp] theorem actualDmemAddr_ext (extAddr finalAddr : BitVec 23) :
    actualDmemAddrPure true extAddr finalAddr = extAddr := rfl

@[simp] theorem actualDmemAddr_normal (extAddr finalAddr : BitVec 23) :
    actualDmemAddrPure false extAddr finalAddr = finalAddr := rfl

@[simp] theorem actualDmemByteWdata_ext (extByte finalByte : BitVec 8) :
    actualDmemByteWdataPure true extByte finalByte = extByte := rfl

@[simp] theorem actualDmemByteWdata_normal (extByte finalByte : BitVec 8) :
    actualDmemByteWdataPure false extByte finalByte = finalByte := rfl

/-- External write covers all 4 byte lanes. -/
@[simp] theorem protoDmemByteWe_ext (finalWe : Bool) :
    protoDmemByteWePure finalWe true = true := by
  unfold protoDmemByteWePure; cases finalWe <;> rfl

@[simp] theorem protoDmemByteWe_normal (finalWe : Bool) :
    protoDmemByteWePure finalWe false = finalWe := by
  unfold protoDmemByteWePure; cases finalWe <;> rfl

/-! ## Composite priority spec -/

/-- External write absolutely wins over pending-AMO and EX-stage. -/
theorem dmemAddr_ext_priority
    (pendingWE : Bool) (extAddr pendWordAddr dmemAddr : BitVec 23) :
    actualDmemAddrPure true extAddr
        (finalDmemAddrPure pendingWE pendWordAddr dmemAddr) = extAddr := by
  rfl

/-- No external, AMO wins over EX-stage. -/
theorem dmemAddr_amo_priority
    (extAddr pendWordAddr dmemAddr : BitVec 23) :
    actualDmemAddrPure false extAddr
        (finalDmemAddrPure true pendWordAddr dmemAddr) = pendWordAddr := by
  rfl

/-- No override → EX-stage. -/
theorem dmemAddr_normal
    (extAddr pendWordAddr dmemAddr : BitVec 23) :
    actualDmemAddrPure false extAddr
        (finalDmemAddrPure false pendWordAddr dmemAddr) = dmemAddr := by
  rfl

/-! ## Signal-level wrappers -/

def finalDmemAddrSignal {dom : DomainConfig}
    (pendingWE : Signal dom Bool)
    (pendWordAddr dmemAddr : Signal dom (BitVec 23)) : Signal dom (BitVec 23) :=
  Signal.mux pendingWE pendWordAddr dmemAddr

def finalDmemByteWdataSignal {dom : DomainConfig}
    (pendingWE : Signal dom Bool)
    (pendByte byteWdata : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux pendingWE pendByte byteWdata

def finalDmemByteWeSignal {dom : DomainConfig}
    (byteWe pendingWE : Signal dom Bool) : Signal dom Bool :=
  byteWe ||| pendingWE

def actualDmemAddrSignal {dom : DomainConfig}
    (extWE : Signal dom Bool)
    (extAddr finalAddr : Signal dom (BitVec 23)) : Signal dom (BitVec 23) :=
  Signal.mux extWE extAddr finalAddr

def actualDmemByteWdataSignal {dom : DomainConfig}
    (extWE : Signal dom Bool)
    (extByte finalByte : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux extWE extByte finalByte

def protoDmemByteWeSignal {dom : DomainConfig}
    (finalWe extWE : Signal dom Bool) : Signal dom Bool :=
  finalWe ||| extWE

end Sparkle.IP.RV32.Bus
