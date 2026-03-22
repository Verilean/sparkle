/-
  CDC Multi-Clock JIT Test

  End-to-end test that:
  1. JIT-compiles DomainA (8-bit counter) and DomainB (accumulator)
  2. Runs them concurrently via JIT.runCDC on separate threads
  3. Verifies message transfer and reports results

  Usage:
    lake exe cdc-multi-clock-test
-/

import Sparkle.Core.JIT

-- Import the synthesis module to ensure generated files exist
import Examples.CDC.MultiClockSim

open Sparkle.Core.JIT

def main : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════╗"
  IO.println "║   Sparkle CDC Multi-Clock JIT Simulation Test   ║"
  IO.println "╠══════════════════════════════════════════════════╣"
  IO.println "║  DomainA: 8-bit counter  (100MHz, 200K cycles)  ║"
  IO.println "║  DomainB: accumulator    ( 50MHz, 100K cycles)  ║"
  IO.println "║  Connected via lock-free SPSC queue             ║"
  IO.println "╚══════════════════════════════════════════════════╝"
  IO.println ""

  -- Step 1: JIT-compile DomainA
  IO.println "JIT: Compiling DomainA (counter)..."
  let handleA ← JIT.compileAndLoad ".lake/build/gen/cdc/domain_a_jit.cpp"
  IO.println "  DomainA loaded."

  -- Step 2: JIT-compile DomainB
  IO.println "JIT: Compiling DomainB (accumulator)..."
  let handleB ← JIT.compileAndLoad ".lake/build/gen/cdc/domain_b_jit.cpp"
  IO.println "  DomainB loaded."

  -- Step 3: Inspect ports
  let numWiresA ← JIT.numWires handleA
  let numWiresB ← JIT.numWires handleB
  IO.println s!"  DomainA wires: {numWiresA}"
  IO.println s!"  DomainB wires: {numWiresB}"

  -- Verify single-step operation of each module
  IO.println ""
  IO.println "--- Single-step verification ---"
  JIT.reset handleA
  for i in [:5] do
    JIT.evalTick handleA
    let out ← JIT.getOutput handleA 0
    IO.println s!"  DomainA cycle {i + 1}: output = {out}"

  JIT.reset handleB
  JIT.setInput handleB 0 42
  for i in [:3] do
    JIT.evalTick handleB
    let out ← JIT.getOutput handleB 0
    IO.println s!"  DomainB cycle {i + 1}: output = {out} (input=42, expected acc={42 * (i + 1)})"

  -- Step 4: Reset both modules for CDC run
  JIT.reset handleA
  JIT.reset handleB

  -- Step 5: Run CDC simulation
  IO.println ""
  IO.println "--- CDC Multi-threaded Run ---"
  IO.println "  Starting JIT.runCDC (DomainA: 200K cycles, DomainB: 100K cycles)..."

  let (sent, received, rollbacks) ← JIT.runCDC handleA handleB 200000 100000 0 0

  IO.println s!"  Messages sent:     {sent}"
  IO.println s!"  Messages received: {received}"
  IO.println s!"  Rollbacks:         {rollbacks}"
  IO.println ""

  -- Step 6: Verify results
  let pass := sent > 0 && received > 0
  if pass then
    IO.println "*** CDC Multi-Clock Test: PASS ***"
  else
    IO.println "*** CDC Multi-Clock Test: FAIL ***"

  JIT.destroy handleA
  JIT.destroy handleB

  return if pass then 0 else 1
