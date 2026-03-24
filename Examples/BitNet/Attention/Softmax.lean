/-
  BitNet Attention — Softmax — Signal DSL

  Fully combinational softmax for fixed seqLen:
    1. Max reduction (comparator tree)
    2. Subtract max from each score
    3. Exp LUT lookup (256-entry mux tree)
    4. Sum reduction (adder tree)
    5. Reciprocal LUT (256-entry mux tree)
    6. Normalize: weight_i = exp_i × recip >> 24
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Generate a 256-entry exp(-i) LUT in Q8.24.
    Index i maps to round(exp(-i) × 2^24). -/
def generateExpLUT : Array Int := Id.run do
  let mut lut : Array Int := #[]
  for i in [:256] do
    if i == 0 then
      lut := lut.push ((2 ^ softmaxFracBits : Nat) : Int)
    else
      let val : Float := Float.exp (-(Float.ofNat i))
      let q8_24 := (val * Float.ofNat (2 ^ softmaxFracBits)).toUInt64.toNat
      lut := lut.push (q8_24 : Int)
  return lut

/-- Generate a 256-entry reciprocal LUT in Q8.24.
    Indexed by top 8 bits of the exp sum. -/
def generateRecipLUT (maxSumBits : Nat) : Array Int := Id.run do
  let mut lut : Array Int := #[]
  let shift := if maxSumBits > 8 then maxSumBits - 8 else 0
  for i in [:256] do
    if i == 0 then
      lut := lut.push ((2 ^ softmaxFracBits : Nat) : Int)
    else
      let sumApprox : Nat := i <<< shift
      if sumApprox == 0 then
        lut := lut.push ((2 ^ softmaxFracBits : Nat) : Int)
      else
        let recip := (2 ^ (2 * softmaxFracBits) : Nat) / sumApprox
        lut := lut.push (recip : Int)
  return lut

/-- Softmax over an array of score signals using Signal DSL.
    Returns Q8.24 attention weights (32-bit). -/
def softmaxSignal (scores : Array (Signal dom (BitVec 32)))
    : Array (Signal dom (BitVec 32)) :=
  if scores.size == 0 then #[]
  else Id.run do
    -- Stage 1: Max reduction (signed comparator tree)
    let maxVal := maxTree scores

    -- Stage 2: Subtract max (diff ≤ 0)
    let mut diffs : Array (Signal dom (BitVec 32)) := #[]
    for score in scores do
      diffs := diffs.push (score - maxVal)

    -- Stage 3: Exp LUT lookup
    let expLUTData := generateExpLUT
    let expTable : Array (BitVec 32) := expLUTData.map (fun i => BitVec.ofInt 32 i)

    let mut expVals : Array (Signal dom (BitVec 32)) := #[]
    for diff in diffs do
      -- Negate diff to get positive index (diff ≤ 0)
      let absDiff := (fun x => 0 - x) <$> diff
      -- Lower 8 bits as index
      let idx := absDiff.map (BitVec.extractLsb' 0 8 ·)
      -- Check upper bits for saturation (if |diff| ≥ 256, exp ≈ 0)
      let upperBits := absDiff.map (BitVec.extractLsb' 8 24 ·)
      let isZero := upperBits === (0 : BitVec 24)
      let isLarge := ~~~isZero
      let satIdx := Signal.mux isLarge (Signal.pure 255#8) idx
      -- LUT lookup via mux tree
      let expVal := lutMuxTree expTable satIdx
      expVals := expVals.push expVal

    -- Stage 4: Sum of exp values
    let expSum := adderTree expVals

    -- Stage 5: Reciprocal LUT (indexed by top 8 bits of sum)
    let recipLUTData := generateRecipLUT 32
    let recipTable : Array (BitVec 32) := recipLUTData.map (fun i => BitVec.ofInt 32 i)
    let recipIdx := expSum.map (BitVec.extractLsb' 24 8 ·)
    let recipVal := lutMuxTree recipTable recipIdx

    -- Stage 6: Normalize — weight_i = (exp_i × recip) >> 24
    let mut weights : Array (Signal dom (BitVec 32)) := #[]
    for expVal in expVals do
      -- Sign-extend to 64 bits for multiplication
      let expExt := signExtendSignal 32 expVal
      let recipExt := signExtendSignal 32 recipVal
      let prod := expExt * recipExt
      -- Shift right by 24 and truncate to 32 bits
      let weight := prod.map (BitVec.extractLsb' 24 32 ·)
      weights := weights.push weight

    return weights

end Sparkle.Examples.BitNet.Attention
