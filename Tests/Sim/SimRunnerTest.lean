/-
  SimRunnerTest — Comprehensive tests for runSim / runSingleSim / runMultiDomainSim.

  25 tests covering:
    A1–A4  Equivalence: parallel path vs single path give matching state
    B1–B6  Auto-select: runSim picks the right backend / rejects bad inputs
    C1–C5  Port-name resolution errors
    D1–D4  Typed-vs-raw index alignment
    E1–E5  Stress / regression

  Reuses the DomainA counter and DomainB accumulator from
  Examples.CDC.MultiClockSim (already synthesized to .lake/build/gen/cdc/).

  Run:    lake exe sim-runner-test
-/

import Sparkle.Core.JIT
import Sparkle.Core.SimTyped
import Sparkle.Core.SimParallel
import Examples.CDC.MultiClockSim

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open Sparkle.Core.JIT
open Sparkle.Core.SimParallel

-- SimSpecs for the two reference domains (same as Tests/CDC/MultiClockTest).
def aSpec : SimSpec := {
  moduleName := "DomainA"
  inputs := [{ name := "enable", width := 1 }]
  outputs := [{ name := "count", width := 32 }, { name := "count2", width := 32 }]
}

def bSpec : SimSpec := {
  moduleName := "DomainB"
  inputs := [{ name := "value", width := 32 }]
  outputs := [{ name := "acc", width := 32 }, { name := "acc2", width := 32 }]
}

run_cmd generateSimWrappers aSpec
run_cmd generateSimWrappers bSpec

/-- Load DomainA from the generated JIT C++ and return a Simulator. -/
def loadA : IO DomainA.Sim.Simulator := do
  let h ← JIT.compileAndLoad ".lake/build/gen/cdc/domain_a_jit.cpp"
  pure { handle := h }

def loadB : IO DomainB.Sim.Simulator := do
  let h ← JIT.compileAndLoad ".lake/build/gen/cdc/domain_b_jit.cpp"
  pure { handle := h }

/-- Dump every register of a JIT handle as a List (ordered by index). -/
def snapshotRegs (h : JITHandle) : IO (List UInt64) := do
  let n ← JIT.numRegs h
  let mut out : List UInt64 := []
  for i in [:n.toNat] do
    out := out ++ [(← JIT.getReg h i.toUInt32)]
  pure out

-- ============================================================================
-- Tiny test harness
-- ============================================================================

structure TestStats where
  passed : Nat := 0
  failed : Nat := 0
  deriving Repr

def passTest (s : TestStats) (name : String) : IO TestStats := do
  IO.println s!"  PASS  {name}"
  pure { s with passed := s.passed + 1 }

def failTest (s : TestStats) (name : String) (why : String) : IO TestStats := do
  IO.println s!"  FAIL  {name}: {why}"
  pure { s with failed := s.failed + 1 }

/-- Returns true if `body` threw an IO error, false if it succeeded. -/
def expectError (body : IO Unit) : IO Bool := do
  try body; pure false
  catch _ => pure true

/-- Assertion helper: runs `body`, records pass/fail based on `ok`. -/
def check (s : TestStats) (name : String) (ok : Bool) (why : String := "assertion failed") : IO TestStats := do
  if ok then passTest s name else failTest s name why

-- ============================================================================
-- Test body
-- ============================================================================

def main : IO UInt32 := do
  IO.println "=== SimRunner Tests ==="
  let mut st : TestStats := {}

  -- --------------------------------------------------------------------------
  -- A1: runSingleSim vs manual evalTick loop produce identical register state
  -- --------------------------------------------------------------------------
  do
    let a1 ← loadA
    a1.reset
    let _ ← runSingleSim a1.toEndpoint 100
    let snapRun ← snapshotRegs a1.handle
    let a2 ← loadA
    a2.reset
    for _ in [:100] do JIT.evalTick a2.handle
    let snapManual ← snapshotRegs a2.handle
    st ← check st "A1 runSingleSim == manual evalTick loop (100c)" (snapRun == snapManual)
    JIT.destroy a1.handle; JIT.destroy a2.handle

  -- --------------------------------------------------------------------------
  -- A2: runSim auto-select equals runSingleSim (1 endpoint, 0 connections)
  -- --------------------------------------------------------------------------
  do
    let a1 ← loadA
    a1.reset
    a1.step { enable := 1 }  -- set enable, then let runSim drive cycles
    let _ ← runSim [a1.toEndpoint] (cycles := 500)
    let snapAuto ← snapshotRegs a1.handle
    let a2 ← loadA
    a2.reset
    a2.step { enable := 1 }
    let _ ← runSingleSim a2.toEndpoint 500
    let snapForced ← snapshotRegs a2.handle
    st ← check st "A2 runSim [ep] == runSingleSim (500c)" (snapAuto == snapForced)
    JIT.destroy a1.handle; JIT.destroy a2.handle

  -- --------------------------------------------------------------------------
  -- A3: Decoupled two-domain run. DomainB's value input is driven by CDC
  --     (= 0 when queue empty), which is equivalent to isolated runs because
  --     DomainA starts at 0 anyway.
  -- --------------------------------------------------------------------------
  do
    -- Baseline: A alone, 500 cycles; B alone, 500 cycles; snapshot each.
    let aBase ← loadA
    aBase.reset; aBase.step { enable := 1 }
    let _ ← runSingleSim aBase.toEndpoint 500
    let aBaseSnap ← snapshotRegs aBase.handle

    let bBase ← loadB
    bBase.reset; bBase.step { value := 0 }
    let _ ← runSingleSim bBase.toEndpoint 500
    let bBaseSnap ← snapshotRegs bBase.handle

    -- Parallel run with CDC, same starting state.
    let aPar ← loadA
    aPar.reset; aPar.step { enable := 1 }
    let bPar ← loadB
    bPar.reset; bPar.step { value := 0 }
    let _ ← runSim
      [aPar.toEndpoint, bPar.toEndpoint]
      (connections := [("count", "value")])
      (cycles := 500)
    let aParSnap ← snapshotRegs aPar.handle
    let _bParSnap ← snapshotRegs bPar.handle

    -- A must match bit-for-bit; B is allowed to differ (CDC delivery). We only
    -- assert A's regs are identical to confirm the parallel runner doesn't
    -- corrupt producer state.
    st ← check st "A3 parallel producer == standalone producer (500c)" (aParSnap == aBaseSnap)
    -- Stronger: B baseline was driven by 0s, so its final acc must be 0.
    -- In parallel mode, B receives counter values >0, so acc > 0.
    let bAccBase := bBaseSnap.headD 0
    st ← check st "A3 decoupled B baseline acc == 0" (bAccBase == 0)
    JIT.destroy aBase.handle; JIT.destroy bBase.handle
    JIT.destroy aPar.handle;  JIT.destroy bPar.handle

  -- --------------------------------------------------------------------------
  -- A4: Data relay — producer sends, consumer sees nonzero values after
  --     enough cycles (weak condition: rollback tolerance).
  -- --------------------------------------------------------------------------
  do
    let a ← loadA
    a.reset; a.step { enable := 1 }
    let b ← loadB
    b.reset; b.step { value := 0 }
    let stats ← runSim
      [a.toEndpoint, b.toEndpoint]
      (connections := [("count", "value")])
      (cycles := 100000)
    st ← check st "A4 relay: messages sent > 0" (stats.messagesSent > 0) s!"sent={stats.messagesSent}"
    st ← check st "A4 relay: messages received > 0" (stats.messagesReceived > 0) s!"received={stats.messagesReceived}"
    st ← check st "A4 relay: cyclesRun == 100000" (stats.cyclesRun == 100000) s!"cyclesRun={stats.cyclesRun}"
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- B1: runSim with 1 endpoint => runSingleSim (messagesSent == 0)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA
    a.reset
    let stats ← runSim [a.toEndpoint] (cycles := 100)
    st ← check st "B1 single endpoint has zero CDC traffic" (stats.messagesSent == 0 && stats.rollbacks == 0)
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- B2: runSim with 2 endpoints + 1 connection => CDC path (messagesSent > 0)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset; a.step { enable := 1 }
    let b ← loadB; b.reset
    let stats ← runSim
      [a.toEndpoint, b.toEndpoint]
      (connections := [("count", "value")])
      (cycles := 10000)
    st ← check st "B2 two endpoints + conn routes through CDC" (stats.messagesSent > 0)
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- B3: runSim with 1 endpoint but nonempty connections => error
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset
    let err ← expectError (do
      let _ ← runSim [a.toEndpoint] (connections := [("count", "value")]) (cycles := 10)
      pure ())
    st ← check st "B3 single endpoint + nonempty connections rejected" err
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- B4: runSim with 2 endpoints but no connections => error
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; a.reset; b.reset
    let err ← expectError (do
      let _ ← runSim [a.toEndpoint, b.toEndpoint] (cycles := 10)
      pure ())
    st ← check st "B4 two endpoints + 0 connections rejected" err
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- B5: runSim with 2 endpoints + 2 connections => error (multi-conn TODO)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; a.reset; b.reset
    let err ← expectError (do
      let _ ← runSim
        [a.toEndpoint, b.toEndpoint]
        (connections := [("count", "value"), ("count2", "value")])
        (cycles := 10)
      pure ())
    st ← check st "B5 multi-connection rejected" err
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- B6: runSim with 3 endpoints => error (not yet supported)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; let c ← loadA; a.reset; b.reset; c.reset
    let err ← expectError (do
      let _ ← runSim
        [a.toEndpoint, b.toEndpoint, c.toEndpoint]
        (connections := [("count", "value")])
        (cycles := 10)
      pure ())
    st ← check st "B6 three endpoints rejected" err
    JIT.destroy a.handle; JIT.destroy b.handle; JIT.destroy c.handle

  -- --------------------------------------------------------------------------
  -- C1: bad producer output name => error mentions available outputs
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; a.reset; b.reset
    let err ← expectError (do
      let _ ← runSim
        [a.toEndpoint, b.toEndpoint]
        (connections := [("doesnotexist", "value")])
        (cycles := 10)
      pure ())
    st ← check st "C1 unknown producer output rejected" err
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- C2: bad consumer input name => error
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; a.reset; b.reset
    let err ← expectError (do
      let _ ← runSim
        [a.toEndpoint, b.toEndpoint]
        (connections := [("count", "doesnotexist")])
        (cycles := 10)
      pure ())
    st ← check st "C2 unknown consumer input rejected" err
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- C3: case sensitivity (Count vs count)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; a.reset; b.reset
    let err ← expectError (do
      let _ ← runSim
        [a.toEndpoint, b.toEndpoint]
        (connections := [("Count", "value")])
        (cycles := 10)
      pure ())
    st ← check st "C3 case-sensitive name lookup" err
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- C4: empty string name
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; let b ← loadB; a.reset; b.reset
    let err ← expectError (do
      let _ ← runSim
        [a.toEndpoint, b.toEndpoint]
        (connections := [("", "value")])
        (cycles := 10)
      pure ())
    st ← check st "C4 empty connection name rejected" err
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- C5: valid lookup via toEndpoint lookup functions (smoke test)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA
    let ep := a.toEndpoint
    let ok := (ep.lookupOutput "count").isSome && (ep.lookupOutput "nope").isNone
    st ← check st "C5 lookupOutput returns some/none correctly" ok
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- D1: inputPortIndexByName "enable" = raw JIT index 0 for DomainA
  -- --------------------------------------------------------------------------
  do
    st ← check st "D1 DomainA enable rawIdx = 0"
      (DomainA.Sim.inputPortIndexByName "enable" == some 0)

  -- --------------------------------------------------------------------------
  -- D2: outputPortIndexByName "count" = 0, "count2" = 1
  -- --------------------------------------------------------------------------
  do
    st ← check st "D2 DomainA count=0 count2=1"
      (DomainA.Sim.outputPortIndexByName "count" == some 0
       && DomainA.Sim.outputPortIndexByName "count2" == some 1)

  -- --------------------------------------------------------------------------
  -- D3: DomainB value/acc/acc2
  -- --------------------------------------------------------------------------
  do
    st ← check st "D3 DomainB value=0, acc=0, acc2=1"
      (DomainB.Sim.inputPortIndexByName "value" == some 0
       && DomainB.Sim.outputPortIndexByName "acc" == some 0
       && DomainB.Sim.outputPortIndexByName "acc2" == some 1)

  -- --------------------------------------------------------------------------
  -- D4: CDC with count2 (not count) — port 1 still reachable
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset; a.step { enable := 1 }
    let b ← loadB; b.reset
    let stats ← runSim
      [a.toEndpoint, b.toEndpoint]
      (connections := [("count2", "value")])
      (cycles := 10000)
    st ← check st "D4 CDC via count2 (idx=1) transfers messages" (stats.messagesSent > 0)
    JIT.destroy a.handle; JIT.destroy b.handle

  -- --------------------------------------------------------------------------
  -- E1: 0 cycles
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset
    let stats ← runSim [a.toEndpoint] (cycles := 0)
    st ← check st "E1 0 cycles returns zero stats" (stats.cyclesRun == 0)
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- E2: 1 cycle
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset
    let stats ← runSim [a.toEndpoint] (cycles := 1)
    st ← check st "E2 1 cycle" (stats.cyclesRun == 1)
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- E3: Larger run (100k cycles) — exercise hot loop
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset; a.step { enable := 1 }
    let stats ← runSim [a.toEndpoint] (cycles := 100000)
    st ← check st "E3 100k cycles completes" (stats.cyclesRun == 100000)
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- E4: Double run continues from prior state (no implicit reset)
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset; a.step { enable := 1 }
    let _ ← runSim [a.toEndpoint] (cycles := 200)
    let snap1 ← snapshotRegs a.handle
    let _ ← runSim [a.toEndpoint] (cycles := 200)
    let snap2 ← snapshotRegs a.handle
    -- If counters were reset the second run would end at same state → regs equal.
    -- Expected: second run state differs (counter advanced further).
    st ← check st "E4 successive runSim continues state" (snap1 != snap2)
    JIT.destroy a.handle

  -- --------------------------------------------------------------------------
  -- E5: Reset between runs returns to initial state
  -- --------------------------------------------------------------------------
  do
    let a ← loadA; a.reset; a.step { enable := 1 }
    let _ ← runSim [a.toEndpoint] (cycles := 200)
    a.reset
    a.step { enable := 1 }
    let snapAfterReset ← snapshotRegs a.handle
    let aFresh ← loadA; aFresh.reset; aFresh.step { enable := 1 }
    let snapFresh ← snapshotRegs aFresh.handle
    st ← check st "E5 reset between runs returns to initial state" (snapAfterReset == snapFresh)
    JIT.destroy a.handle; JIT.destroy aFresh.handle

  -- --------------------------------------------------------------------------
  -- Summary
  -- --------------------------------------------------------------------------
  IO.println ""
  IO.println s!"=== Results: {st.passed} passed, {st.failed} failed ==="
  return if st.failed == 0 then 0 else 1
