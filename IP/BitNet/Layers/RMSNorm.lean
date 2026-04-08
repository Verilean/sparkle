/-
  BitNet Layers — RMSNorm — Signal DSL

  RMSNorm: y_i = x_i × rsqrt(mean(x²)) × scale_i

  Implemented as a combinational function operating on arrays.
  The sequential FSM version (multi-cycle) can be added later
  using Signal.loop for hardware synthesis.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Configuration for RMSNorm layer -/
structure RMSNormConfig where
  dim       : Nat
  sqAccBits : Nat := 76
  lutBits   : Nat := 8
  deriving Repr, BEq

/-- Compute 1/N as a Q8.24 fixed-point constant -/
def reciprocalQ8_24 (n : Nat) : Int :=
  (2 ^ scaleFracBits : Int) / n

/-- Generate a 256-entry rsqrt LUT in Q8.24. -/
def generateRsqrtLUT : Array Int := Id.run do
  let mut lut : Array Int := #[]
  for i in [:256] do
    if i == 0 then
      lut := lut.push ((2 ^ scaleFracBits : Nat) : Int)
    else
      let val : Float := Float.ofNat (i * (2 ^ 16))
      let rsqrt := 1.0 / Float.sqrt val
      let q8_24 := (rsqrt * Float.ofNat (2 ^ scaleFracBits)).toUInt64.toNat
      lut := lut.push (q8_24 : Int)
  return lut

/-- Combinational RMSNorm using Signal DSL.
    Processes all elements simultaneously.

    For simulation/testing: applies RMSNorm spec directly.
    For synthesis: would need Signal.loop FSM (future work). -/
def rmsNormSignal (xs : Array (Signal dom (BitVec 32)))
    (scales : Array (Signal dom (BitVec 32)))
    : Array (Signal dom (BitVec 32)) :=
  -- Build sum-of-squares using adder tree
  let squaredSignals : Array (Signal dom (BitVec 64)) := xs.map (fun x =>
    let xExt := signExtendSignal 32 x
    xExt * xExt)
  let sumSq := adderTree squaredSignals

  -- Multiply by 1/N and extract mean (approximate via extracting representative bits)
  let recipN := reciprocalQ8_24 xs.size
  let meanApprox := sumSq.map (fun s =>
    let si := s.toInt
    let mean := si * recipN / (2 ^ scaleFracBits : Int)
    BitVec.ofInt 32 mean)

  -- LUT index: extract bits [23:16] of mean
  let lutIdx := meanApprox.map (BitVec.extractLsb' 16 8 ·)

  -- rsqrt LUT lookup
  let rsqrtLUTData := generateRsqrtLUT
  let rsqrtTable : Array (BitVec 32) := rsqrtLUTData.map (fun i => BitVec.ofInt 32 i)
  let rsqrtVal := lutMuxTree rsqrtTable lutIdx

  -- Normalize each element: y_i = (x_i × rsqrt_val) >> 24 × scale_i >> 24
  Id.run do
    let mut outputs : Array (Signal dom (BitVec 32)) := #[]
    for i in [:xs.size] do
      if i < scales.size then
        -- x × rsqrt (64-bit intermediate)
        let xExt := signExtendSignal 32 xs[i]!
        let rsqrtExt := signExtendSignal 32 rsqrtVal
        let normProd := xExt * rsqrtExt
        let normShifted := normProd.map (BitVec.extractLsb' 24 32 ·)
        -- Apply scale: normalized × scale >> 24
        let normExt := signExtendSignal 32 normShifted
        let scaleExt := signExtendSignal 32 scales[i]!
        let scaledProd := normExt * scaleExt
        let result := scaledProd.map (BitVec.extractLsb' 24 32 ·)
        outputs := outputs.push result
    return outputs

end Sparkle.IP.BitNet.Layers
