/-
  BitNet Layers — RMSNorm — Signal DSL

  RMSNorm: y_i = x_i × rsqrt(mean(x²)) × scale_i

  Fully combinational, synthesizable implementation.
  sum-of-squares via adder tree, mean via fixed-point multiply by 1/N,
  rsqrt via 256-entry LUT, normalize each element.
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

/-- Compute 1/N as a Q8.24 fixed-point constant (elab time) -/
def reciprocalQ8_24 (n : Nat) : Int :=
  (2 ^ scaleFracBits : Int) / n

/-- Generate a 256-entry rsqrt LUT in Q8.24 (elab time). -/
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

/-- 16-entry rsqrt LUT in Q8.24, indexed by top 4 bits of mean.
    Sampled from the 256-entry table at indices 0,16,32,...,240.
    Pre-computed via `#eval generateRsqrtLUT`. -/
def rsqrtLUT16 : Array (BitVec 32) := #[
  0x1000000#32, 0x4000#32, 0x2d41#32, 0x24f3#32,
  0x2000#32, 0x1c9f#32, 0x1a20#32, 0x1830#32,
  0x16a0#32, 0x1555#32, 0x143d#32, 0x134b#32,
  0x1279#32, 0x11c0#32, 0x111a#32, 0x1086#32
]

/-- Square a list of signals and return 64-bit results (elab-time list build). -/
@[reducible] def squareList : List (Signal dom (BitVec 32))
    → List (Signal dom (BitVec 64))
  | [] => []
  | x :: rest =>
    let xExt := signExtendSignal 32 x
    (xExt * xExt) :: squareList rest

/-- Normalize each element: y_i = (x_i × rsqrt) >> 24 × scale_i >> 24.
    List-based structural recursion for synthesis. -/
@[reducible] def normalizeList (rsqrtVal : Signal dom (BitVec 32))
    : List (Signal dom (BitVec 32) × Signal dom (BitVec 32))
    → List (Signal dom (BitVec 32))
  | [] => []
  | (x, scale) :: rest =>
    let xExt := signExtendSignal 32 x
    let rsqrtExt := signExtendSignal 32 rsqrtVal
    let normProd := xExt * rsqrtExt
    let normShifted := normProd.map (BitVec.extractLsb' 24 32 ·)
    let normExt := signExtendSignal 32 normShifted
    let scaleExt := signExtendSignal 32 scale
    let scaledProd := normExt * scaleExt
    let result := scaledProd.map (BitVec.extractLsb' 24 32 ·)
    result :: normalizeList rsqrtVal rest

/-- Simplified RMSNorm for toy models (dim ≤ 16).
    Uses 16-entry rsqrt LUT (4-bit index) to keep mux tree small.
    `recipN` is 1/dim in Q8.24 — pass as a literal (e.g. 0x400000#32
    for dim=4) because Nat.pow does not reduce through synthesis. -/
def rmsNormSignal (xs : Array (Signal dom (BitVec 32)))
    (scales : Array (Signal dom (BitVec 32)))
    (recipN : BitVec 32)
    : Array (Signal dom (BitVec 32)) :=
  -- 1. Sum of squares via adder tree (64-bit domain)
  let squared := squareList xs.toList
  let sumSq := treeReduce (· + ·) (Signal.pure 0) squared

  -- 2. Mean = sumSq × (1/N) in fixed-point
  let sumSqHi : Signal dom (BitVec 32) :=
    Signal.map (BitVec.extractLsb' 0 32 ·) sumSq
  let sumSqExt : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 sumSqHi
  let recipExt : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 (Signal.pure recipN)
  let meanProd : Signal dom (BitVec 48) := sumSqExt * recipExt
  let meanApprox : Signal dom (BitVec 32) := Signal.map (BitVec.extractLsb' 24 32 ·) meanProd

  -- 3. LUT index: extract bits [27:24] of mean (4-bit index → 16-entry LUT)
  let lutIdx : Signal dom (BitVec 4) := Signal.map (BitVec.extractLsb' 24 4 ·) meanApprox

  -- 4. rsqrt LUT: 16-entry, pre-computed at elab time
  let rsqrtVal := lutMuxTree rsqrtLUT16 lutIdx

  -- 5. Normalize: y_i = (x_i × rsqrt) >> 24 × scale_i >> 24
  let pairs := xs.toList.zip scales.toList
  (normalizeList rsqrtVal pairs).toArray

end Sparkle.IP.BitNet.Layers
