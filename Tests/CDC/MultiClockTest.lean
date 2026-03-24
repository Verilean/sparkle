/-
  CDC Multi-Clock JIT Test — Type-Safe Version

  End-to-end test using typed simulation wrappers:
  1. JIT-compiles DomainA (8-bit counter) and DomainB (accumulator)
  2. Uses typed SimInput/SimOutput/Simulator (no raw port indices)
  3. Runs CDC simulation via JIT.runCDC with typed port index constants
  4. Verifies message transfer and reports results

  Usage:
    lake exe cdc-multi-clock-test
-/

import Sparkle.Core.JIT
import Sparkle.Core.SimTyped

-- Import the synthesis module to ensure generated files exist
import Examples.CDC.MultiClockSim

open Sparkle.Core.JIT

-- ============================================================================
-- Type-safe wrappers for DomainA and DomainB
-- ============================================================================

-- DomainA: 8-bit counter — input: enable (Bool=1-bit), output: count (32-bit) x2
def domainASpec : SimSpec := {
  moduleName := "DomainA"
  inputs := [{ name := "enable", width := 1 }]
  outputs := [{ name := "count", width := 32 }, { name := "count2", width := 32 }]
}

-- DomainB: accumulator — input: value (32-bit), output: acc (32-bit) x2
def domainBSpec : SimSpec := {
  moduleName := "DomainB"
  inputs := [{ name := "value", width := 32 }]
  outputs := [{ name := "acc", width := 32 }, { name := "acc2", width := 32 }]
}

-- Generate typed wrappers at compile time
run_cmd generateSimWrappers domainASpec
run_cmd generateSimWrappers domainBSpec

open DomainA.Sim
open DomainB.Sim

def main : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════╗"
  IO.println "║   Sparkle CDC Multi-Clock JIT Simulation Test   ║"
  IO.println "║   (Type-Safe Wrappers — No Raw Port Indices)    ║"
  IO.println "╠══════════════════════════════════════════════════╣"
  IO.println "║  DomainA: 8-bit counter  (100MHz, 200K cycles)  ║"
  IO.println "║  DomainB: accumulator    ( 50MHz, 100K cycles)  ║"
  IO.println "║  Connected via lock-free SPSC queue             ║"
  IO.println "╚══════════════════════════════════════════════════╝"
  IO.println ""

  -- Step 1: JIT-compile both domains
  IO.println "JIT: Compiling DomainA (counter)..."
  let handleA ← JIT.compileAndLoad ".lake/build/gen/cdc/domain_a_jit.cpp"
  IO.println "  DomainA loaded."

  IO.println "JIT: Compiling DomainB (accumulator)..."
  let handleB ← JIT.compileAndLoad ".lake/build/gen/cdc/domain_b_jit.cpp"
  IO.println "  DomainB loaded."

  -- Step 2: Type-safe single-step verification
  IO.println ""
  IO.println "--- Single-step verification (typed API) ---"

  let simA : DomainA.Sim.Simulator := { handle := handleA }
  simA.reset
  for i in [:5] do
    simA.step { enable := 1 }              -- BitVec 1 — type-safe!
    let out ← simA.read                     -- SimOutput { count : BitVec 32 }
    IO.println s!"  DomainA cycle {i + 1}: count = {out.count}"

  let simB : DomainB.Sim.Simulator := { handle := handleB }
  simB.reset
  for i in [:3] do
    simB.step { value := 42 }              -- BitVec 32 — type-safe!
    let out ← simB.read                     -- SimOutput { acc : BitVec 32 }
    IO.println s!"  DomainB cycle {i + 1}: acc = {out.acc} (expected {42 * (i + 1)})"

  -- Step 3: CDC simulation
  simA.reset
  simB.reset

  IO.println ""
  IO.println "--- CDC Multi-threaded Run ---"
  IO.println "  Starting JIT.runCDC (DomainA: 200K cycles, DomainB: 100K cycles)..."

  -- Use typed port index constants instead of hardcoded 0
  let (sent, received, rollbacks) ← JIT.runCDC
    handleA handleB 200000 100000
    DomainA.Sim.outputPortIndex_count    -- typed: UInt32
    DomainB.Sim.inputPortIndex_value     -- typed: UInt32

  IO.println s!"  Messages sent:     {sent}"
  IO.println s!"  Messages received: {received}"
  IO.println s!"  Rollbacks:         {rollbacks}"
  IO.println ""

  -- Step 4: Verify results
  let pass := sent > 0 && received > 0
  if pass then
    IO.println "*** CDC Multi-Clock Test: PASS ***"
  else
    IO.println "*** CDC Multi-Clock Test: FAIL ***"

  JIT.destroy handleA
  JIT.destroy handleB

  return if pass then 0 else 1
