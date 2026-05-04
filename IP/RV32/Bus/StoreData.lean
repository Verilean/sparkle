/-
  RV32 store byte-data lane formation — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 600..608). For a 32-bit
  store, each of the four DRAM byte lanes receives a particular byte
  of `rs2` depending on the store width (funct3):

      funct3  | width | byte0 | byte1 | byte2 | byte3
      --------|-------|-------|-------|-------|-------
      000 SB  | byte  | rs2[0]| rs2[0]| rs2[0]| rs2[0]
      001 SH  | half  | rs2[0]| rs2[1]| rs2[0]| rs2[1]
      010 SW  | word  | rs2[0]| rs2[1]| rs2[2]| rs2[3]

  where `rs2[i]` is the i-th byte of `rs2`. The DRAM byte-enable mask
  (`StoreWidth.lean`) selects which lanes actually get written; this
  file is just about the data the lane carries — even unselected
  lanes carry a defined value (no don't-cares — easier to reason about
  in proofs).

  In SoC.lean's encoding:

      byte0_wdata = rs2_byte0                                                -- always
      byte1_wdata = if isSB then rs2_byte0 else rs2_byte1                    -- SB replicates
      byte2_wdata = if isSW then rs2_byte2 else rs2_byte0                    -- SW vs broadcast
      byte3_wdata = if isSW then rs2_byte3
                    else (if isSB then rs2_byte0 else rs2_byte1)             -- SH high half

  The "broadcast rs2[0]" pattern for SB matches RISC-V hardware — the
  chosen lane comes from the byte-enable mask, but every lane sees
  rs2[0], so reading a too-wide range from the bus during a SB still
  shows the byte0 (which simplifies fanout in synthesis).

  Reference: RISC-V unprivileged spec §2.6 (Loads and Stores).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure byte-data lane functions -/

/-- Lane-0 data: always rs2[7:0]. -/
@[inline] def byte0WdataPure (rs2_byte0 : BitVec 8) : BitVec 8 :=
  rs2_byte0

/-- Lane-1 data: SB → rs2[7:0]; SW/SH/other → rs2[15:8]. -/
@[inline] def byte1WdataPure
    (isSB : Bool) (rs2_byte0 rs2_byte1 : BitVec 8) : BitVec 8 :=
  if isSB then rs2_byte0 else rs2_byte1

/-- Lane-2 data: SW → rs2[23:16]; otherwise → rs2[7:0] (broadcast for SB,
    SH-low; for SH-high the byte-enable suppresses lane 2 anyway). -/
@[inline] def byte2WdataPure
    (isSW : Bool) (rs2_byte0 rs2_byte2 : BitVec 8) : BitVec 8 :=
  if isSW then rs2_byte2 else rs2_byte0

/-- Lane-3 data: SW → rs2[31:24]; SB → rs2[7:0]; SH → rs2[15:8]. -/
@[inline] def byte3WdataPure
    (isSB isSW : Bool)
    (rs2_byte0 rs2_byte1 rs2_byte3 : BitVec 8) : BitVec 8 :=
  if isSW then rs2_byte3
  else if isSB then rs2_byte0 else rs2_byte1

/-! ## Spec invariants — closed by `rfl` -/

@[simp] theorem byte0Wdata_rfl (rs2_byte0 : BitVec 8) :
    byte0WdataPure rs2_byte0 = rs2_byte0 := rfl

@[simp] theorem byte1Wdata_SB
    (rs2_byte0 rs2_byte1 : BitVec 8) :
    byte1WdataPure true rs2_byte0 rs2_byte1 = rs2_byte0 := rfl

@[simp] theorem byte1Wdata_notSB
    (rs2_byte0 rs2_byte1 : BitVec 8) :
    byte1WdataPure false rs2_byte0 rs2_byte1 = rs2_byte1 := rfl

@[simp] theorem byte2Wdata_SW
    (rs2_byte0 rs2_byte2 : BitVec 8) :
    byte2WdataPure true rs2_byte0 rs2_byte2 = rs2_byte2 := rfl

@[simp] theorem byte2Wdata_notSW
    (rs2_byte0 rs2_byte2 : BitVec 8) :
    byte2WdataPure false rs2_byte0 rs2_byte2 = rs2_byte0 := rfl

@[simp] theorem byte3Wdata_SW
    (isSB : Bool) (rs2_byte0 rs2_byte1 rs2_byte3 : BitVec 8) :
    byte3WdataPure isSB true rs2_byte0 rs2_byte1 rs2_byte3 = rs2_byte3 := rfl

@[simp] theorem byte3Wdata_SB_notSW
    (rs2_byte0 rs2_byte1 rs2_byte3 : BitVec 8) :
    byte3WdataPure true false rs2_byte0 rs2_byte1 rs2_byte3 = rs2_byte0 := rfl

@[simp] theorem byte3Wdata_default
    (rs2_byte0 rs2_byte1 rs2_byte3 : BitVec 8) :
    byte3WdataPure false false rs2_byte0 rs2_byte1 rs2_byte3 = rs2_byte1 := rfl

/-! ## SW-broadcast: every lane gets its own byte -/

theorem sw_lanes_match
    (isSB : Bool) (rs2_byte0 rs2_byte1 rs2_byte2 rs2_byte3 : BitVec 8) :
    byte0WdataPure rs2_byte0 = rs2_byte0 ∧
    byte1WdataPure false rs2_byte0 rs2_byte1 = rs2_byte1 ∧
    byte2WdataPure true rs2_byte0 rs2_byte2 = rs2_byte2 ∧
    byte3WdataPure isSB true rs2_byte0 rs2_byte1 rs2_byte3 = rs2_byte3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## SB-broadcast: every lane gets rs2[7:0] (the byte-enable will pick) -/

theorem sb_lanes_broadcast
    (rs2_byte0 rs2_byte1 rs2_byte2 rs2_byte3 : BitVec 8) :
    byte0WdataPure rs2_byte0 = rs2_byte0 ∧
    byte1WdataPure true rs2_byte0 rs2_byte1 = rs2_byte0 ∧
    byte2WdataPure false rs2_byte0 rs2_byte2 = rs2_byte0 ∧
    byte3WdataPure true false rs2_byte0 rs2_byte1 rs2_byte3 = rs2_byte0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## SH-low (addr[1]=0): lanes 0,1 get rs2[7:0]/rs2[15:8] -/

theorem sh_low_lanes
    (rs2_byte0 rs2_byte1 : BitVec 8) :
    byte0WdataPure rs2_byte0 = rs2_byte0 ∧
    byte1WdataPure false rs2_byte0 rs2_byte1 = rs2_byte1 := by
  refine ⟨rfl, rfl⟩

/-! ## Signal-level wrappers -/

def byte0WdataSignal {dom : DomainConfig}
    (rs2_byte0 : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  rs2_byte0

def byte1WdataSignal {dom : DomainConfig}
    (isSB : Signal dom Bool)
    (rs2_byte0 rs2_byte1 : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux isSB rs2_byte0 rs2_byte1

def byte2WdataSignal {dom : DomainConfig}
    (isSW : Signal dom Bool)
    (rs2_byte0 rs2_byte2 : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux isSW rs2_byte2 rs2_byte0

def byte3WdataSignal {dom : DomainConfig}
    (isSB isSW : Signal dom Bool)
    (rs2_byte0 rs2_byte1 rs2_byte3 : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux isSW rs2_byte3 (Signal.mux isSB rs2_byte0 rs2_byte1)

end Sparkle.IP.RV32.Bus
