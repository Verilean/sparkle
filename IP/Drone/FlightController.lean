/-
  Drone Flight Controller — BitNet Neural FC — Signal DSL

  Ultra-low-latency neural flight controller using ternary BitNet.
  Replaces traditional PID with a learned ternary neural network.

  Architecture:
    IMU (6 inputs) → RMSNorm → FFN layer 1 → FFN layer 2 → Motor output (4)

  Fully combinational for minimum latency.
  dim=16, 2 layers, no attention (sensor fusion only, not sequential).

  Input:  6 × 16-bit signed (accel_xyz, gyro_xyz) — Q8.8 fixed-point
  Output: 4 × 16-bit signed (motor_1..4) — Q8.8 PWM duty

  Estimated latency @ 200 MHz:
    Combinational: ~20 ns (adder trees + scale multiplies)
    Pipelined (1 register): ~5 ns per stage, 4 stages = 20 ns total

  Resource estimate:
    ~500 LUT, ~100 FF, 2-4 DSP48 (for scale multiplies)
    Fits on Zynq-7010 / ECP5-25K / iCE40 UP5K
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.ResidualAdd

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Layers

variable {dom : DomainConfig}

-- ============================================================
-- Toy weights (all +1 for initial testing)
-- Real weights come from training on flight data
-- ============================================================

/-- Pack 6 sensor inputs into dim=16 activation vector.
    Sensors are zero-padded to dim=16. -/
@[reducible] def sensorPack
    (accelX accelY accelZ gyroX gyroY gyroZ : Signal dom (BitVec 32))
    : List (Signal dom (BitVec 32)) :=
  [ accelX, accelY, accelZ, gyroX, gyroY, gyroZ,
    Signal.pure 0#32, Signal.pure 0#32,
    Signal.pure 0#32, Signal.pure 0#32,
    Signal.pure 0#32, Signal.pure 0#32,
    Signal.pure 0#32, Signal.pure 0#32,
    Signal.pure 0#32, Signal.pure 0#32 ]

/-- Single FFN layer (dim=16) — fully combinational.
    All +1 weights, so BitLinear = sum of activations.
    Uses explicit adder chain for guaranteed synthesis. -/
def ffnLayer16
    (scaleVal : Signal dom (BitVec 32))
    (residualInput : Signal dom (BitVec 32))
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  -- BitLinear (all +1): sum all 16 activations via adder tree
  let sum0 := (a0 + a1) + (a2 + a3)
  let sum1 := (a4 + a5) + (a6 + a7)
  let sum2 := (a8 + a9) + (a10 + a11)
  let sum3 := (a12 + a13) + (a14 + a15)
  let gateAcc := (sum0 + sum1) + (sum2 + sum3)
  -- Scale
  let gateAcc48 := signExtendSignal 16 gateAcc
  let gateScaled := scaleMultiplySignal gateAcc48 scaleVal
  let gateActivated := reluSqSignal gateScaled
  -- Up path (same sum)
  let upScaled := scaleMultiplySignal (signExtendSignal 16 gateAcc) scaleVal
  -- ElemMul
  let elemResult := elemMulSignal gateActivated upScaled
  -- Down path (single element)
  let downAcc48 := signExtendSignal 16 elemResult
  let downScaled := scaleMultiplySignal downAcc48 scaleVal
  -- Residual
  residualAddSignal residualInput downScaled

/-- Output projection: dim=16 → 4 motor outputs.
    Each motor output = BitLinear (4 different weight rows × dim=16). -/
@[reducible] def motorProjectList
    (activations : Array (Signal dom (BitVec 32)))
    : List (Array Int) → List (Signal dom (BitVec 32))
  | [] => []
  | weights :: rest =>
    bitLinearSignal weights activations :: motorProjectList activations rest

/-- BitNet Neural Flight Controller — combinational, ultra-low-latency.

    Inputs: 6 × 32-bit sensor values (Q16.16)
      accelX, accelY, accelZ — accelerometer
      gyroX, gyroY, gyroZ — gyroscope

    Weights: passed as parameters (from training)
      layer1Gate/Up/Down, layer2Gate/Up/Down — FFN weights (dim=16 each)
      motorWeights — 4 × dim=16 output projection weights
      scaleVal — Q8.24 scale constant

    Output: 4 motor PWM values packed as (m1 × (m2 × (m3 × m4))) -/
def neuralFlightController
    (accelX accelY accelZ : Signal dom (BitVec 32))
    (gyroX gyroY gyroZ : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))) :=
  let z := (Signal.pure 0#32 : Signal dom (BitVec 32))
  let sc := (Signal.pure 0x01000000#32 : Signal dom (BitVec 32))

  -- Layer 1: sensors → FFN
  let l1out := ffnLayer16 sc accelX
    accelX accelY accelZ gyroX gyroY gyroZ z z z z z z z z z z

  -- Layer 2: l1out broadcast → FFN
  let l2out := ffnLayer16 sc l1out
    l1out l1out l1out l1out l1out l1out l1out l1out
    l1out l1out l1out l1out l1out l1out l1out l1out

  -- Output: 4 motors = 16× l2out sum (all +1 weights)
  -- For different motors, weights would differ; for test, all same
  let motorVal := l2out + l2out + l2out + l2out +
                  l2out + l2out + l2out + l2out +
                  l2out + l2out + l2out + l2out +
                  l2out + l2out + l2out + l2out

  bundle2 motorVal (bundle2 motorVal (bundle2 motorVal motorVal))

-- ============================================================
-- Default weights for testing (identity-ish: all +1)
-- ============================================================

def defaultWeights16 : Array Int :=
  #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
def defaultMotorWeights : Array (Array Int) := #[
  #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
]
def defaultScale : Int := 0x01000000

/-- Top-level flight controller with default (test) weights. -/
def droneFC
    (accelX accelY accelZ : Signal dom (BitVec 32))
    (gyroX gyroY gyroZ : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))) :=
  neuralFlightController accelX accelY accelZ gyroX gyroY gyroZ

end Sparkle.IP.Drone
