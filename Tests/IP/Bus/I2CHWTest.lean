/-
  Sim test for IP.Bus.I2CHW.i2cMasterHW.

  Behavioural check: kick off a transaction and walk the FSM
  for enough cycles to reach every state at least once.
  Print the trace so a human can eyeball it (or a follow-up
  refinement can pin down cycle-accurate expectations).

  Synth via #synthesizeVerilog on the FSM state output
  (single-scalar).
-/

import IP.Bus.I2C
import IP.Bus.I2CHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.I2CHW

namespace Sparkle.Tests.IP.Bus.I2CHWTest

abbrev D := defaultDomain

def main : IO Unit := do
  IO.println "=== I2C HW master FSM (state trajectory) ==="

  let mut ok := true

  -- bitDiv = 1 for fast walk-through (each tick every 2 cycles).
  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let bitDivSig : Signal D (BitVec 16) := Signal.pure 1#16
  let addrSig : Signal D (BitVec 7) := Signal.pure 0x50#7
  let rwSig : Signal D Bool := Signal.pure false  -- write
  let dataSig : Signal D (BitVec 8) := Signal.pure 0xA5#8
  -- Slave ACKs everything (SDA pulled low during ACK slot).
  let sdaFromBus : Signal D Bool := Signal.pure false

  let master := i2cMasterHW startSig bitDivSig addrSig rwSig dataSig sdaFromBus

  -- Walk 80 cycles; expect to see states 0..6 all appear.
  let mut seen : Array Bool := Array.replicate 8 false
  for t in [:80] do
    let s := (master.state.val t).toNat
    if s < 8 then
      seen := seen.set! s true
  IO.println "  state visitation:"
  for i in [:7] do
    IO.println s!"    state {i}: {seen[i]!}"

  -- We expect states 0 (idle), 1 (startC), 2 (addr), 3 (ackA),
  -- 4 (data), 5 (ackD), 6 (stopC) all visited.
  for i in [:7] do
    if !seen[i]! then
      IO.println s!"  UNEXPECTED: state {i} not visited"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.I2CHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.I2CHW

private def synth_i2cMasterState
    (start : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16))
    (addr : Signal defaultDomain (BitVec 7))
    (rw : Signal defaultDomain Bool)
    (dataByte : Signal defaultDomain (BitVec 8))
    (sdaFromBus : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 3) :=
  (i2cMasterHW start bitDiv addr rw dataByte sdaFromBus).state

#synthesizeVerilog synth_i2cMasterState

end SynthesisChecks
