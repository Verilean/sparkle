/-
  DRAM Interface — Pure Model + Signal Interface

  A simple external memory interface shared by H.264 encoder and decoder.
  Models frame buffer and bitstream buffer with AXI-lite-inspired handshake.

  Pure model: HashMap-based simulation (IO.Ref)
  Signal interface: Ports passed through (external DRAM controller at top level)

  Interface:
    Request:  reqValid, reqWrite, reqAddr(24), reqWData(32)
    Response: respValid, respRData(32)

  Address space: 16M words × 32-bit (24-bit address, 64MB total)
-/

import Sparkle
import Sparkle.Compiler.Elab
import Std.Data.HashMap

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.Video.H264.DRAMInterface

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- Pure DRAM Model (for simulation and proofs)
-- ============================================================================

/-- Pure DRAM state: partial function from address to data.
    Unwritten addresses return 0. -/
structure DRAMState where
  mem : List (BitVec 24 × BitVec 32)
  deriving Repr

/-- Initial empty DRAM -/
def DRAMState.empty : DRAMState := ⟨[]⟩

/-- Read from DRAM: returns the most recent write to the address, or 0 -/
def DRAMState.read (s : DRAMState) (addr : BitVec 24) : BitVec 32 :=
  match s.mem.find? (fun p => p.1 == addr) with
  | some (_, v) => v
  | none => 0#32

/-- Write to DRAM: prepend (addr, data) — most recent write shadows older ones -/
def DRAMState.write (s : DRAMState) (addr : BitVec 24) (data : BitVec 32) : DRAMState :=
  ⟨(addr, data) :: s.mem⟩

/-- Erase all entries for a given address (used in proofs) -/
def DRAMState.erase (s : DRAMState) (addr : BitVec 24) : DRAMState :=
  ⟨s.mem.filter (fun p => p.1 != addr)⟩

-- ============================================================================
-- IO-based simulation model (for JIT/test integration)
-- ============================================================================

/-- Mutable DRAM simulation using IO.Ref with Std.HashMap -/
structure DRAMSim where
  ref : IO.Ref (Std.HashMap UInt64 UInt32)

def DRAMSim.new : IO DRAMSim := do
  let r ← IO.mkRef (Std.HashMap.emptyWithCapacity)
  pure ⟨r⟩

def DRAMSim.read (sim : DRAMSim) (addr : BitVec 24) : IO (BitVec 32) := do
  let m ← sim.ref.get
  let key := addr.toNat.toUInt64
  match m[key]? with
  | some v => pure (BitVec.ofNat 32 v.toNat)
  | none => pure 0#32

def DRAMSim.write (sim : DRAMSim) (addr : BitVec 24) (data : BitVec 32) : IO Unit := do
  let m ← sim.ref.get
  sim.ref.set (m.insert addr.toNat.toUInt64 data.toNat.toUInt32)

/-- Bulk load data starting at base address -/
def DRAMSim.loadBlock (sim : DRAMSim) (baseAddr : BitVec 24) (data : Array (BitVec 32))
    : IO Unit := do
  for i in [:data.size] do
    let addr := baseAddr + BitVec.ofNat 24 i
    if h : i < data.size then
      sim.write addr data[i]

/-- Bulk read data starting at base address -/
def DRAMSim.readBlock (sim : DRAMSim) (baseAddr : BitVec 24) (count : Nat)
    : IO (Array (BitVec 32)) := do
  let mut result := Array.mkEmpty count
  for i in [:count] do
    let addr := baseAddr + BitVec.ofNat 24 i
    let v ← sim.read addr
    result := result.push v
  pure result

-- ============================================================================
-- Signal-level DRAM interface (for synthesis)
-- ============================================================================

-- DRAM controller state (1-cycle read latency model)
declare_signal_state DRAMCtrlState
  | respValid : Bool       := false
  | respRData : BitVec 32  := 0#32

/-- Simple DRAM controller with 1-cycle read latency.
    For synthesis: ports are passed through to external memory.
    For simulation: uses Signal.memory for internal storage.

    Inputs:
      reqValid  — request valid
      reqWrite  — true = write, false = read
      reqAddr   — 24-bit address (only lower bits used for internal memory)
      reqWData  — 32-bit write data

    Outputs:
      (respValid, respRData) — response valid + read data (1-cycle latency) -/
def dramController {dom : DomainConfig}
    (reqValid : Signal dom Bool)
    (reqWrite : Signal dom Bool)
    (reqAddr : Signal dom (BitVec 24))
    (reqWData : Signal dom (BitVec 32))
    : Signal dom (Bool × BitVec 32) :=
  -- Use lower 8 bits of address for internal memory (256 words)
  let memAddr := .map (BitVec.extractLsb' 0 8) reqAddr
  -- Write enable: valid AND write
  let writeEn := reqValid &&& reqWrite
  -- Read: valid AND NOT write
  let readValid := reqValid &&& (~~~reqWrite)
  -- Memory with 1-cycle read latency
  let memData := Signal.memory memAddr reqWData writeEn memAddr
  -- Response: register the read valid and data
  let respValid := Signal.register false readValid
  let respRData := Signal.register 0#32 memData
  bundle2 respValid respRData

-- ============================================================================
-- Address map constants for H.264 encoder/decoder
-- ============================================================================

/-- Frame buffer base address (pixels: 16M words for up to 4K frames) -/
def frameBufBase : BitVec 24 := 0x000000#24

/-- Bitstream buffer base address -/
def bitstreamBufBase : BitVec 24 := 0x400000#24

/-- Coefficient buffer base address -/
def coeffBufBase : BitVec 24 := 0x800000#24

/-- Reconstruction buffer base address -/
def reconBufBase : BitVec 24 := 0xC00000#24

end Sparkle.IP.Video.H264.DRAMInterface
