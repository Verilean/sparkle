/-
  Neural Motion Controller — BitNet Whole-Body — Signal DSL

  Replaces traditional PD + IK + trajectory planning with a single
  neural network that maps sensor state to joint commands.

  Input (36 values):
    - 30 × joint encoder angles (14-bit, zero-extended to 32-bit)
    - 6 × IMU (accel XYZ + gyro XYZ, 16-bit extended to 32-bit)

  Output (30 values):
    - 30 × target servo positions (16-bit)

  Architecture: dim=64, 3 FFN layers (wider and deeper than drone FC)
    Layer 1: 36 inputs → dim=64 (sensor fusion)
    Layer 2: dim=64 → dim=64 (nonlinear transform)
    Layer 3: dim=64 → 30 outputs (joint commands)

  Fully combinational for ultra-low latency.
  All ternary weights (+1, 0, -1).

  Estimated latency: ~30-50 ns (3 layers × adder tree + scale)
  Estimated resources: ~2000 LUT, ~48 DSP
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.ResidualAdd

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Layers

variable {dom : DomainConfig}

/-- Single FFN layer for dim=64, explicit adder tree.
    All +1 ternary weights (test config).
    Takes a list of activations, returns single output. -/
def ffnLayer64
    (scaleVal : Signal dom (BitVec 32))
    (residualInput : Signal dom (BitVec 32))
    (activations : List (Signal dom (BitVec 32)))
    : Signal dom (BitVec 32) :=
  -- BitLinear: sum all activations (all +1 weights)
  let gateAcc := treeReduce (· + ·) (Signal.pure 0#32 : Signal dom (BitVec 32)) activations
  -- Scale
  let gateAcc48 := signExtendSignal 16 gateAcc
  let gateScaled := scaleMultiplySignal gateAcc48 scaleVal
  let gateActivated := reluSqSignal gateScaled
  -- Up path (same sum for test weights)
  let upScaled := scaleMultiplySignal (signExtendSignal 16 gateAcc) scaleVal
  -- ElemMul
  let elemResult := elemMulSignal gateActivated upScaled
  -- Down path
  let downAcc48 := signExtendSignal 16 elemResult
  let downScaled := scaleMultiplySignal downAcc48 scaleVal
  -- Residual
  residualAddSignal residualInput downScaled

/-- Output projection: dim=64 activations → 1 output value.
    BitLinear with all +1 weights (test config). -/
def outputProject
    (activations : List (Signal dom (BitVec 32)))
    : Signal dom (BitVec 32) :=
  treeReduce (· + ·) (Signal.pure 0#32 : Signal dom (BitVec 32)) activations

/-- Neural whole-body motion controller.

    Input: 36 sensor values (30 encoders + 6 IMU) as 32-bit Q16.16.
    Output: 30 servo target positions as 32-bit.

    Architecture:
      Layer 1: 36 inputs → 1 intermediate (broadcast to 64)
      Layer 2: 64 → 1 intermediate (broadcast to 64)
      Layer 3: 64 → 30 outputs (one outputProject per joint)

    For synthesis tractability, intermediate activations are broadcast
    (same value to all dim=64 positions). Real training would use
    different weights per position. -/
def neuralMotionController
    -- 30 encoder values (32-bit each)
    (enc : List (Signal dom (BitVec 32)))
    -- 6 IMU values (32-bit each)
    (imu : List (Signal dom (BitVec 32)))
    : List (Signal dom (BitVec 32)) :=
  let sc := (Signal.pure 0x01000000#32 : Signal dom (BitVec 32))
  let z := (Signal.pure 0#32 : Signal dom (BitVec 32))

  -- Combine all 36 inputs
  let allInputs := enc ++ imu

  -- Layer 1: 36 inputs → intermediate
  let l1out := ffnLayer64 sc (allInputs.headD z) allInputs

  -- Broadcast l1out to 64-element list for layer 2
  let l1broadcast := List.replicate 64 l1out

  -- Layer 2: 64 → intermediate
  let l2out := ffnLayer64 sc l1out l1broadcast

  -- Broadcast l2out for output projection
  let l2broadcast := List.replicate 64 l2out

  -- Layer 3: 64 → 30 joint outputs (each is a sum of 64 activations)
  -- For test: all joints get the same output (different weights would differentiate)
  List.replicate 30 (outputProject l2broadcast)

/-- Packaged motion controller with explicit I/O signals.
    Takes 6 key joint angles + IMU, outputs 6 key servo commands.
    (Simplified from 30 for synthesis test — full 30 is structurally identical.)

    Returns (servo0 × (servo1 × (servo2 × (servo3 × (servo4 × servo5))))). -/
def motionController6DOF
    (enc0 enc1 enc2 enc3 enc4 enc5 : Signal dom (BitVec 32))
    (accelX accelY accelZ gyroX gyroY gyroZ : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32))))) :=
  let sc := (Signal.pure 0x01000000#32 : Signal dom (BitVec 32))
  let z := (Signal.pure 0#32 : Signal dom (BitVec 32))

  -- 12 inputs: 6 encoders + 6 IMU
  let inputs := [enc0, enc1, enc2, enc3, enc4, enc5,
                 accelX, accelY, accelZ, gyroX, gyroY, gyroZ]

  -- Layer 1: 12 inputs → intermediate
  let l1out := ffnLayer64 sc enc0 inputs

  -- Broadcast to 12 for layer 2
  let l1b := [l1out, l1out, l1out, l1out, l1out, l1out,
              l1out, l1out, l1out, l1out, l1out, l1out]

  -- Layer 2
  let l2out := ffnLayer64 sc l1out l1b

  -- Output: 6 servos (each = l2out for test weights)
  -- Different trained weights would produce different per-joint commands
  let s0 := l2out
  let s1 := l2out
  let s2 := l2out
  let s3 := l2out
  let s4 := l2out
  let s5 := l2out

  bundle2 s0 (bundle2 s1 (bundle2 s2 (bundle2 s3 (bundle2 s4 s5))))

end Sparkle.IP.Humanoid
