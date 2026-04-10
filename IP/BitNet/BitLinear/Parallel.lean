/-
  BitNet BitLinear — Fully Parallel Core — Signal DSL

  dim-wide parallel ternary MAC array with adder tree reduction.
  Compute takes 1 clock cycle. Weights stored in register array,
  loaded from external memory before computation.

  FSM: IDLE → LOAD_WEIGHTS → COMPUTE → DONE

  During LOAD_WEIGHTS: external memory writes 2-bit weights into
  a register file (1 weight per clock, dim cycles).
  During COMPUTE: all dim MACs fire simultaneously, adder tree
  produces result in 1 combinational cycle.

  For dim=2048: 2048 parallel adders, one 11-level adder tree.
  U280 resource: ~65K LUT (5% of 1.3M available).
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.BitLinear

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Parallel BitLinear with weight register file.

    Weight loading: write 2-bit weights via wAddr/wData/wEn, dim cycles.
    Computation: activation broadcast × all weights → adder tree → result.

    Uses memoryComboRead for weight storage (synthesizes to distributed RAM
    on Xilinx, BRAM on larger configs).

    FSM: 0=IDLE, 1=LOAD, 2=COMPUTE, 3=DONE -/
def bitLinearParallel
    (dim : Nat)
    -- Weight write port
    (wAddr : Signal dom (BitVec 16))
    (wData : Signal dom (BitVec 2))
    (wEn : Signal dom Bool)
    -- Control
    (start : Signal dom Bool)
    -- Activation input (broadcast to all MACs)
    (activation : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (Bool × BitVec 4)) :=
  -- Phase FSM
  let fsm := Signal.loop (dom := dom) (α := BitVec 4 × BitVec 32)
    fun (self : Signal dom (BitVec 4 × BitVec 32)) =>
    let phase := Signal.fst self
    let resultLatch := Signal.snd self

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))

    -- Weight memory: written externally during LOAD, read combinationally during COMPUTE
    -- Build dim parallel reads from the weight memory
    -- Each address reads a 2-bit ternary code

    -- Parallel MAC: for each weight index, read weight and compute contribution
    -- Build the MAC array as a list of (weight_code → ±activation or 0)
    let macList := (List.range dim).map fun i =>
      let addr : Signal dom (BitVec 16) := (Signal.pure (BitVec.ofNat 16 i) : Signal dom (BitVec 16))
      let wCode := Signal.memoryComboRead wAddr wData wEn addr
      let isPlus  : Signal dom Bool := wCode === (Signal.pure 0b10#2 : Signal dom (BitVec 2))
      let isMinus : Signal dom Bool := wCode === (Signal.pure 0b00#2 : Signal dom (BitVec 2))
      Signal.mux isPlus activation
        (Signal.mux isMinus (-(activation : Signal dom (BitVec 32))) (Signal.pure 0#32 : Signal dom (BitVec 32)))

    -- Adder tree reduction
    let macResult : Signal dom (BitVec 32) :=
      treeReduce (· + ·) (Signal.pure 0#32 : Signal dom (BitVec 32)) macList

    -- Start pulse → latch result
    let goIdle : Signal dom Bool := Signal.mux isIdle start (Signal.pure false : Signal dom Bool)
    -- In this parallel design, compute is instant (1 cycle)
    -- IDLE + start → DONE (skip LOAD/COMPUTE phases — weights are always in memory)
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 3#4 : Signal dom (BitVec 4))  -- IDLE → DONE
        (Signal.mux (phase === (Signal.pure 3#4 : Signal dom (BitVec 4)))
          (Signal.mux start (Signal.pure 3#4 : Signal dom (BitVec 4)) phase)
          phase)

    let nextResult : Signal dom (BitVec 32) :=
      Signal.mux goIdle macResult resultLatch

    bundle2 (Signal.register 0#4 nextPhase) (Signal.register 0#32 nextResult)

  let phase := Signal.fst fsm
  let result := Signal.snd fsm
  let done : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

  bundle2 result (bundle2 done phase)

/-- Extract result. -/
def parallelResult (out : Signal dom (BitVec 32 × (Bool × BitVec 4)))
    : Signal dom (BitVec 32) := Signal.fst out

/-- Extract done flag. -/
def parallelDone (out : Signal dom (BitVec 32 × (Bool × BitVec 4)))
    : Signal dom Bool := Signal.fst (Signal.snd out)

end Sparkle.IP.BitNet.BitLinear
