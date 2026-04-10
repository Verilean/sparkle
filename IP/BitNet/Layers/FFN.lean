/-
  BitNet Layers — FFN Block — Signal DSL

  Wires the complete FFN (Feed-Forward Network) datapath:

    input ──► gate_BitLinear ──► Scale ──► ReLU² ──┐
           └──► up_BitLinear   ──► Scale ────────────┤
                                                      ▼
                                               ElemMul(gate, up)
                                                      │
                                                      ▼
                                          down_BitLinear ──► Scale
                                                              │
                                                              ▼
                                                 ResidualAdd(input, down)
                                                              │
                                                              ▼
                                                         output

  In Signal DSL, composition is direct function application — no
  emitInstance or module wiring needed.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Core
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.RMSNorm

namespace Sparkle.IP.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear

variable {dom : DomainConfig}

/-- Configuration for the complete FFN block -/
structure FFNConfig where
  hiddenDim     : Nat
  ffnDim        : Nat
  baseBitWidth  : Nat := 32
  pipelineEvery : Nat := 0
  deriving Repr, BEq

/-- Complete FFN datapath as Signal DSL function composition.

    Takes activation array and per-layer weights/scales,
    returns the output activation. -/
def ffnBlockSignal
    (gateWeights upWeights downWeights : Array Int)
    (gateScaleVal upScaleVal downScaleVal : Int)
    (residualInput : Signal dom (BitVec 32))
    (activations : Array (Signal dom (BitVec 32)))
    : Signal dom (BitVec 32) :=
  -- Gate path: BitLinear → Scale → ReLU²
  let gateAcc := bitLinearSignal gateWeights activations
  let gateAcc48 := signExtendSignal 16 gateAcc
  let gateScaled := scaleMultiplySignal gateAcc48 (Signal.pure (BitVec.ofInt 32 gateScaleVal))
  let gateActivated := reluSqSignal gateScaled

  -- Up path: BitLinear → Scale
  let upAcc := bitLinearSignal upWeights activations
  let upAcc48 := signExtendSignal 16 upAcc
  let upScaled := scaleMultiplySignal upAcc48 (Signal.pure (BitVec.ofInt 32 upScaleVal))

  -- Element-wise multiply: gate × up
  let elemResult := elemMulSignal gateActivated upScaled

  -- Down path: BitLinear → Scale
  let downAcc := bitLinearSignal downWeights #[elemResult]
  let downAcc48 := signExtendSignal 16 downAcc
  let downScaled := scaleMultiplySignal downAcc48 (Signal.pure (BitVec.ofInt 32 downScaleVal))

  -- Residual add: input + down
  residualAddSignal residualInput downScaled

end Sparkle.IP.BitNet.Layers
