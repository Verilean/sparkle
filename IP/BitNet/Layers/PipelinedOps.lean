/-
  BitNet Layers — Pipelined combinational operations — Signal DSL

  Versions of ReLU², ElemMul, and ResidualAdd with pipeline registers
  after each multiply. Breaks critical path for 200 MHz.

  Each adds 1 cycle latency.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Pipelined ReLU²: max(0,x)² with pipeline register after squaring.
    Latency: 1 cycle. -/
def reluSqPipelined (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let signBit := Signal.map (BitVec.extractLsb' 31 1 ·) x
  let isNeg : Signal dom Bool := signBit === (Signal.pure 1#1 : Signal dom (BitVec 1))
  let xExt := signExtendSignal 32 x
  let squared : Signal dom (BitVec 64) := xExt * xExt
  -- Pipeline register after squaring
  let squaredReg := Signal.register (0 : BitVec 64) squared
  let shifted := Signal.map (BitVec.extractLsb' 16 32 ·) squaredReg
  -- isNeg must also be delayed 1 cycle to match
  let isNegReg := Signal.register false isNeg
  Signal.mux isNegReg (Signal.pure 0#32 : Signal dom (BitVec 32)) shifted

/-- Pipelined ElemMul: (a × b) >>> 16 with pipeline register.
    Latency: 1 cycle. -/
def elemMulPipelined (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let aExt := signExtendSignal 32 a
  let bExt := signExtendSignal 32 b
  let prod : Signal dom (BitVec 64) := aExt * bExt
  -- Pipeline register
  let prodReg := Signal.register (0 : BitVec 64) prod
  Signal.map (BitVec.extractLsb' 16 32 ·) prodReg

end Sparkle.IP.BitNet.Layers
