/-
  Hespera Types

  BitVec type aliases and ternary encoding helpers for the BitLinear engine.
  Ternary encoding (i2_s format): 00=-1, 01=0, 10=+1
-/

import IP.BitNet.Config

namespace Sparkle.IP.BitNet

/-- 256-bit packed ternary word (128 weights × 2 bits) -/
abbrev PackedWord := BitVec romWordBits

/-- 32-bit Q16.16 signed activation -/
abbrev Activation := BitVec actTotalBits

/-- 48-bit signed accumulator -/
abbrev Accumulator := BitVec accBits

/-- 32-bit Q8.24 signed scale factor -/
abbrev ScaleFactor := BitVec scaleTotalBits

/-- Ternary value: -1, 0, or +1 -/
inductive Ternary where
  | negOne : Ternary
  | zero   : Ternary
  | posOne : Ternary
  deriving Repr, BEq, DecidableEq

/-- Extract 2-bit ternary code from a packed word at position `idx` (0..127) -/
def extractTernaryCode (word : PackedWord) (idx : Nat) : BitVec 2 :=
  let shiftAmt := idx * 2
  (word >>> shiftAmt).truncate 2

/-- Decode 2-bit code to ternary value
    00 → -1, 01 → 0, 10 → +1, 11 → 0 (invalid, treated as zero) -/
def decodeTernary (code : BitVec 2) : Ternary :=
  if code == 0b00#2 then .negOne
  else if code == 0b10#2 then .posOne
  else .zero

/-- Decode ternary to integer for arithmetic -/
def ternaryToInt (t : Ternary) : Int :=
  match t with
  | .negOne => -1
  | .zero   =>  0
  | .posOne =>  1

/-- Sign-extend a 32-bit value to 48 bits (pure Lean) -/
def signExtend32to48 (val : BitVec 32) : BitVec 48 :=
  val.signExtend 48

/-- Fixed-point multiply: (acc48 * scale32) >>> 24, result truncated to 32 bits -/
def fixedPointScale (acc : Accumulator) (scale : ScaleFactor) : Activation :=
  let accInt := acc.toInt
  let scaleInt := scale.toInt
  let product := accInt * scaleInt
  let shifted := product / (2 ^ scaleFracBits)  -- arithmetic right shift by 24
  BitVec.ofInt actTotalBits shifted

/-- Compute ternary dot product of a packed word with activation slice (pure Lean)
    Returns the partial sum contribution from one group of 128 elements. -/
def ternaryDotGroup (word : PackedWord) (activations : Array Activation) : Accumulator :=
  Id.run do
    let mut acc : Int := 0
    for i in [:groupSize] do
      let code := extractTernaryCode word i
      let t := decodeTernary code
      let actVal := if h : i < activations.size then (activations[i]).toInt else 0
      acc := acc + ternaryToInt t * actVal
    return BitVec.ofInt accBits acc

/-- ReLU²: max(0,x)² in Q16.16. Square gives Q32.32, shift right 16 → Q16.16 -/
def reluSquared (x : Activation) : Activation :=
  let xi := x.toInt
  if xi ≤ 0 then BitVec.ofNat actTotalBits 0
  else
    let sq := xi * xi  -- Q32.32
    let shifted := sq / (2 ^ 16)  -- back to Q16.16
    BitVec.ofInt actTotalBits shifted

/-- Element-wise multiply in Q16.16: (a*b) >>> 16 -/
def elemMul (a b : Activation) : Activation :=
  let ai := a.toInt
  let bi := b.toInt
  let product := ai * bi  -- Q32.32
  let shifted := product / (2 ^ 16)  -- back to Q16.16
  BitVec.ofInt actTotalBits shifted

/-- Saturating signed 32-bit addition for residual connections -/
def residualAdd (a b : Activation) : Activation :=
  let ai := a.toInt
  let bi := b.toInt
  let sum := ai + bi
  let maxVal : Int := 2^31 - 1
  let minVal : Int := -(2^31)
  if sum > maxVal then BitVec.ofInt actTotalBits maxVal
  else if sum < minVal then BitVec.ofInt actTotalBits minVal
  else BitVec.ofInt actTotalBits sum

/-- 8-bit signed quantized activation (INT8) for attention Q/K -/
abbrev QActivation := BitVec qkvBits

/-- Quantize Q16.16 activation to INT8 with configurable shift and saturation.
    shifted = x >>> quantShift, then clamp to [-128, 127] -/
def quantizeToInt8 (x : Activation) (quantShift : Nat) : QActivation :=
  let xi := x.toInt
  let shifted := xi / (2 ^ quantShift : Int)
  if shifted > 127 then BitVec.ofNat qkvBits 127
  else if shifted < -128 then BitVec.ofInt qkvBits (-128)
  else BitVec.ofInt qkvBits shifted

/-- INT8 dot product: sum of element-wise signed products (pure Lean reference) -/
def int8DotProduct (a b : Array QActivation) : Int :=
  Id.run do
    let n := min a.size b.size
    let mut sum : Int := 0
    for i in [:n] do
      let ai := if h : i < a.size then a[i].toInt else 0
      let bi := if h : i < b.size then b[i].toInt else 0
      sum := sum + ai * bi
    return sum

/-- Scaled dot-product score: dot(Q,K) / 2^shift -/
def scaledScore (a b : Array QActivation) (shift : Nat) : Int :=
  int8DotProduct a b / (2 ^ shift : Int)

/-- Q8.24 attention weight (softmax output) -/
abbrev AttentionWeight := BitVec softmaxTotalBits

/-- Find maximum value in a score array -/
def maxScore (scores : Array Int) : Int :=
  if scores.size == 0 then 0
  else Id.run do
    let mut best := scores[0]!
    for i in [1:scores.size] do
      if scores[i]! > best then
        best := scores[i]!
    return best

/-- Approximate exp(x) in Q8.24 via Float.
    Input x should be non-positive (from softmax subtract-max). -/
def expQ8_24 (x : Int) : Int :=
  let xf := Float.ofInt x
  let result := Float.exp xf * Float.ofNat (2^softmaxFracBits)
  result.toUInt64.toNat

/-- Reference softmax: subtract max → exp → normalize.
    Returns Q8.24 weights that sum to approximately 2^24. -/
def softmaxRef (scores : Array Int) : Array Int :=
  if scores.size == 0 then #[]
  else Id.run do
    let m := maxScore scores
    -- Compute exp(score_i - max) for each
    let mut exps : Array Int := #[]
    for i in [:scores.size] do
      exps := exps.push (expQ8_24 (scores[i]! - m))
    -- Sum of exps
    let mut total : Int := 0
    for e in exps do
      total := total + e
    -- Normalize: weight_i = exp_i × 2^24 / total
    let mut weights : Array Int := #[]
    for e in exps do
      if total > 0 then
        weights := weights.push (e * (2^softmaxFracBits : Nat) / total)
      else
        weights := weights.push 0
    return weights

/-- Weighted V sum for one output element j:
    out[j] = Σ_i weight[i] × V[i][j] / 2^24
    where weight[i] is Q8.24 and V[i][j] is INT8 -/
def weightedVSum (weights : Array Int) (vMatrix : Array (Array Int)) (j : Nat) : Int :=
  Id.run do
    let mut acc : Int := 0
    for i in [:weights.size] do
      let w := weights[i]!
      let v := if h : i < vMatrix.size then
        let row := vMatrix[i]
        if hj : j < row.size then row[j] else 0
      else 0
      acc := acc + w * v
    return acc / (2^softmaxFracBits : Int)

end Sparkle.IP.BitNet
