/-
  CDC Multi-Clock Simulation — End-to-End Demonstration

  Two hardware modules in different clock domains, connected via
  the lock-free SPSC queue (JIT.runCDC):

  - DomainA (Fast Producer, 100MHz): 8-bit counter, outputs count value.
  - DomainB (Slow Consumer, 50MHz): Receives value on input port,
    accumulates it into an internal register.

  The test:
  1. Synthesizes both modules to C++ via #writeDesign
  2. JIT-compiles and loads each as a separate shared library
  3. Calls JIT.runCDC to run them on separate threads with CDC queue
  4. Reports messages sent/received and rollback count
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.JIT

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Examples.CDC.MultiClockSim

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro
open Sparkle.Core.JIT

-- ============================================================================
-- DomainA: 8-bit counter (Fast Producer)
--
-- Input: enable (Bool). Output: (count(32), count(32)).
-- Each cycle when enabled: count := count + 1  (wraps at 256)
-- Output includes count as 32-bit zero-extended.
-- ============================================================================

declare_signal_state CounterState
  | count : BitVec 8 := 0#8

private def counterBody {dom : DomainConfig}
    (enable : Signal dom Bool) (state : Signal dom CounterState)
    : Signal dom CounterState :=
  let count := CounterState.count state
  let incCount := count + 1#8
  let nextCount := Signal.mux enable incCount count
  bundleAll! [
    Signal.register 0#8 nextCount
  ]

def domainACounter {dom : DomainConfig}
    (enable : Signal dom Bool)
    : Signal dom (BitVec 32 × BitVec 32) :=
  let state := Signal.loop (counterBody enable)
  let count := CounterState.count state
  let countU32 := 0#24 ++ count
  bundleAll! [countU32, countU32]

-- Synthesize DomainA
#writeDesign domainACounter
  ".lake/build/gen/cdc/domain_a.sv"
  ".lake/build/gen/cdc/domain_a_cppsim.h"

-- ============================================================================
-- DomainB: Accumulator (Slow Consumer)
--
-- Input: 32-bit value from CDC queue.
-- Output: (accumulator(32), accumulator(32)).
-- Each cycle: acc := acc + input
-- ============================================================================

declare_signal_state AccState
  | acc : BitVec 32 := 0#32

private def accBody {dom : DomainConfig}
    (input : Signal dom (BitVec 32)) (state : Signal dom AccState)
    : Signal dom AccState :=
  let acc := AccState.acc state
  let nextAcc := acc + input
  bundleAll! [
    Signal.register 0#32 nextAcc
  ]

def domainBAccumulator {dom : DomainConfig}
    (input : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × BitVec 32) :=
  let state := Signal.loop (accBody input)
  let acc := AccState.acc state
  bundleAll! [acc, acc]

-- Synthesize DomainB
#writeDesign domainBAccumulator
  ".lake/build/gen/cdc/domain_b.sv"
  ".lake/build/gen/cdc/domain_b_cppsim.h"

end Examples.CDC.MultiClockSim
