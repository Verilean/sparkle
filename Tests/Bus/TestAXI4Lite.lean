/-
  AXI4-Lite Bus Protocol — Simulation Tests

  Verifies handshake correctness via cycle-accurate simulation:
  1. Single write transaction
  2. Single read transaction
  3. Write priority over simultaneous read
  4. Valid persistence (BVALID/RVALID hold until ready)
-/

import Sparkle
import IP.Bus.AXI4Lite.Slave
import LSpec

namespace Sparkle.Tests.Bus.AXI4Lite

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.AXI4Lite.Slave
open LSpec

/-- Create a stimulus signal from a list of values (repeats last value) -/
private def stimBool (vals : List Bool) : Signal defaultDomain Bool :=
  ⟨fun t => vals.getD t (vals.getLast?.getD false)⟩

private def stimBV32 (vals : List (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  ⟨fun t => vals.getD t (vals.getLast?.getD 0#32)⟩

private def stimBV4 (vals : List (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  ⟨fun t => vals.getD t (vals.getLast?.getD 0#4)⟩

/-- Run AXI4-Lite slave simulation and return outputs at each cycle -/
private def runSlave
    (awaddr_v  : List (BitVec 32))
    (awvalid_v : List Bool)
    (wdata_v   : List (BitVec 32))
    (wstrb_v   : List (BitVec 4))
    (wvalid_v  : List Bool)
    (bready_v  : List Bool)
    (araddr_v  : List (BitVec 32))
    (arvalid_v : List Bool)
    (rready_v  : List Bool)
    (cycles : Nat)
    : IO (List (Bool × Bool × Bool × Bool × Bool)) := do
  let awaddr  := stimBV32 awaddr_v
  let awvalid := stimBool awvalid_v
  let wdata   := stimBV32 wdata_v
  let wstrb   := stimBV4 wstrb_v
  let wvalid  := stimBool wvalid_v
  let bready  := stimBool bready_v
  let araddr  := stimBV32 araddr_v
  let arvalid := stimBool arvalid_v
  let rready  := stimBool rready_v
  let memRdata : Signal defaultDomain (BitVec 32) := Signal.pure 0xDEADBEEF#32

  let out ← Signal.loopMemo fun state =>
    axi4LiteSlaveBody awaddr awvalid wdata wstrb wvalid bready araddr arvalid rready state

  let fsm := AXI4LiteSlaveState.fsm out

  -- Extract channel outputs from state
  let isIdle := fun t => (fsm.val t) == 0#2
  let isWriteResp := fun t => (fsm.val t) == 1#2
  let isReadResp := fun t => (fsm.val t) == 2#2

  let mut results : List (Bool × Bool × Bool × Bool × Bool) := []
  for t in [:cycles] do
    let awrdy := isIdle t
    let wrdy  := isIdle t
    let bvld  := isWriteResp t
    let arrdy := isIdle t && !(awvalid.val t && wvalid.val t)
    let rvld  := isReadResp t
    results := results ++ [(awrdy, wrdy, bvld, arrdy, rvld)]
  return results

def allTests : IO TestSeq := do
  -- ============================================================
  -- Test 1: Single write transaction
  -- t=0: AWVALID=1, WVALID=1 → slave accepts (AWREADY=1, WREADY=1)
  -- t=1: Slave in WriteResp → BVALID=1
  -- t=1: BREADY=1 → handshake completes
  -- t=2: Back to Idle
  -- ============================================================
  let writeResults ← runSlave
    [0x1000#32]           -- awaddr
    [true, false, false]  -- awvalid
    [0xCAFE#32]           -- wdata
    [0xF#4]               -- wstrb
    [true, false, false]  -- wvalid
    [false, true, false]  -- bready (assert at t=1)
    [0#32]                -- araddr
    [false, false, false] -- arvalid
    [false, false, false] -- rready
    3

  -- ============================================================
  -- Test 2: Single read transaction
  -- t=0: ARVALID=1 → slave accepts (ARREADY=1)
  -- t=1: Slave in ReadResp → RVALID=1
  -- t=1: RREADY=1 → handshake completes
  -- t=2: Back to Idle
  -- ============================================================
  let readResults ← runSlave
    [0#32]                -- awaddr
    [false, false, false] -- awvalid
    [0#32]                -- wdata
    [0#4]                 -- wstrb
    [false, false, false] -- wvalid
    [false, false, false] -- bready
    [0x2000#32]           -- araddr
    [true, false, false]  -- arvalid
    [false, true, false]  -- rready (assert at t=1)
    3

  -- ============================================================
  -- Test 3: Write priority over simultaneous read
  -- t=0: AWVALID=1, WVALID=1, ARVALID=1 → write wins
  -- ============================================================
  let priorityResults ← runSlave
    [0x1000#32]           -- awaddr
    [true, false, false]  -- awvalid
    [0xBEEF#32]           -- wdata
    [0xF#4]               -- wstrb
    [true, false, false]  -- wvalid
    [false, true, false]  -- bready
    [0x2000#32]           -- araddr
    [true, false, false]  -- arvalid (simultaneous with write)
    [false, false, false] -- rready
    3

  -- ============================================================
  -- Test 4: Valid persistence — BVALID holds until BREADY
  -- t=0: Write accepted
  -- t=1: BVALID=1, BREADY=0 → stays WriteResp
  -- t=2: BVALID=1, BREADY=1 → completes
  -- t=3: Back to Idle
  -- ============================================================
  let persistResults ← runSlave
    [0x1000#32]                     -- awaddr
    [true, false, false, false]     -- awvalid
    [0xCAFE#32]                     -- wdata
    [0xF#4]                         -- wstrb
    [true, false, false, false]     -- wvalid
    [false, false, true, false]     -- bready (delayed to t=2)
    [0#32]                          -- araddr
    [false, false, false, false]    -- arvalid
    [false, false, false, false]    -- rready
    4

  -- Extract fields: (awready, wready, bvalid, arready, rvalid)
  let wr := writeResults
  let rd := readResults
  let pr := priorityResults
  let ps := persistResults

  -- Helper to extract fields from (awready, wready, bvalid, arready, rvalid)
  let awrdy (r : List (Bool × Bool × Bool × Bool × Bool)) (t : Nat) := (r.getD t default).1
  let bvld  (r : List (Bool × Bool × Bool × Bool × Bool)) (t : Nat) := (r.getD t default).2.2.1
  let arrdy (r : List (Bool × Bool × Bool × Bool × Bool)) (t : Nat) := (r.getD t default).2.2.2.1
  let rvld  (r : List (Bool × Bool × Bool × Bool × Bool)) (t : Nat) := (r.getD t default).2.2.2.2

  return group "AXI4-Lite Slave" (
    group "Single Write" (
      test "t0: awready" (awrdy wr 0 == true) $
      test "t0: bvalid=0" (bvld wr 0 == false) $
      test "t1: bvalid" (bvld wr 1 == true) $
      test "t1: awready=0" (awrdy wr 1 == false) $
      test "t2: idle" (awrdy wr 2 == true)
    ) ++
    group "Single Read" (
      test "t0: arready" (arrdy rd 0 == true) $
      test "t0: rvalid=0" (rvld rd 0 == false) $
      test "t1: rvalid" (rvld rd 1 == true) $
      test "t1: awready=0" (awrdy rd 1 == false) $
      test "t2: idle" (awrdy rd 2 == true)
    ) ++
    group "Write Priority" (
      test "t0: arready=0" (arrdy pr 0 == false) $
      test "t1: bvalid" (bvld pr 1 == true) $
      test "t1: rvalid=0" (rvld pr 1 == false)
    ) ++
    group "Valid Persistence" (
      test "t1: bvalid" (bvld ps 1 == true) $
      test "t2: bvalid persists" (bvld ps 2 == true) $
      test "t3: idle" (awrdy ps 3 == true)
    )
  )

def runMain : IO UInt32 := do
  let tests ← allTests
  lspecIO (Std.HashMap.ofList [("all", [tests])]) []

end Sparkle.Tests.Bus.AXI4Lite

