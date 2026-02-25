/-
  RTL Golden Value Validation

  Validates RTL spec functions (reluSquared, elemMul, residualAdd,
  fixedPointScale, quantizeToInt8) against real model data from bitnet.cpp
  golden values (Tests/golden-values/).

  Proves that the fixed-point RTL spec handles real-world magnitudes correctly,
  not just small toy examples.

  Self-contained: no FFI dependencies.
-/

import Examples.BitNet.Config
import Examples.BitNet.Types

namespace Sparkle.Examples.BitNet.Tests.RTLGoldenValidation

open Sparkle.Examples.BitNet

-- ============================================================================
-- Float32 binary loading (self-contained, no FFI)
-- ============================================================================

/-- Convert IEEE 754 float32 bit pattern to Lean Float (float64) -/
private def float32BitsToFloat64 (bits : UInt32) : Float :=
  let sign := (bits >>> 31) &&& 1
  let exp := (bits >>> 23) &&& 0xFF
  let mantissa := bits &&& 0x7FFFFF
  if exp == 0 && mantissa == 0 then
    if sign == 1 then -0.0 else 0.0
  else if exp == 0xFF then
    if mantissa == 0 then
      let infBits : UInt64 := 0x7FF0000000000000
      let signBit : UInt64 := sign.toUInt64 <<< 63
      Float.ofBits (signBit ||| infBits)
    else
      Float.ofBits 0x7FF8000000000000
  else if exp == 0 then
    let frac := mantissa.toFloat / (2.0 ^ 23.0)
    let value := frac * (2.0 ^ (-126.0 : Float))
    if sign == 1 then -value else value
  else
    let f64Sign := sign.toUInt64 <<< 63
    let f64Exp := ((exp.toUInt64 - 127) + 1023) <<< 52
    let f64Mantissa := mantissa.toUInt64 <<< 29
    Float.ofBits (f64Sign ||| f64Exp ||| f64Mantissa)

/-- Load Float32 array from binary file (little-endian) -/
def loadFloatArrayFromFile (path : String) : IO (Array Float) := do
  let bytes ← IO.FS.readBinFile path
  let numFloats := bytes.size / 4
  let mut result := #[]
  for i in [0:numFloats] do
    let offset := i * 4
    if offset + 4 <= bytes.size then
      let b0 := bytes.get! offset |>.toUInt32
      let b1 := bytes.get! (offset + 1) |>.toUInt32
      let b2 := bytes.get! (offset + 2) |>.toUInt32
      let b3 := bytes.get! (offset + 3) |>.toUInt32
      let bits := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
      result := result.push (float32BitsToFloat64 bits)
  return result

-- ============================================================================
-- Metrics (self-contained)
-- ============================================================================

private def dotProduct (a b : Array Float) : Float :=
  if a.size != b.size then 0.0
  else
    let products := Array.zipWith (· * ·) a b
    products.foldl (· + ·) 0.0

private def l2Norm (arr : Array Float) : Float :=
  Float.sqrt (dotProduct arr arr)

private def computeCosineSimilarity (reference predicted : Array Float) : Float :=
  if reference.size != predicted.size then 0.0
  else if reference.isEmpty then 1.0
  else
    let dot := dotProduct reference predicted
    let normRef := l2Norm reference
    let normPred := l2Norm predicted
    if normRef == 0.0 || normPred == 0.0 then 0.0
    else dot / (normRef * normPred)

private def computeMaxAbsError (reference predicted : Array Float) : Float :=
  if reference.size != predicted.size then 1.0e308
  else if reference.isEmpty then 0.0
  else
    let errors := Array.zipWith (fun r p => Float.abs (p - r)) reference predicted
    errors.foldl (fun acc x => if x > acc then x else acc) 0.0

structure SimpleReport where
  size : Nat
  cosineSimilarity : Float
  maxAbsError : Float

private def generateReport (reference predicted : Array Float) : SimpleReport :=
  { size := reference.size
    cosineSimilarity := computeCosineSimilarity reference predicted
    maxAbsError := computeMaxAbsError reference predicted }

-- ============================================================================
-- Q16.16 <-> Float Conversion (same pattern as Tests/TestComparison.lean)
-- ============================================================================

/-- Convert Float to Q16.16 fixed-point -/
def float_to_q16_16 (f : Float) : Activation :=
  let scaled := f * Float.ofNat (2^16)
  if scaled >= 0.0 then
    BitVec.ofInt 32 (Int.ofNat scaled.toUInt64.toNat)
  else
    let posScaled := (-scaled)
    BitVec.ofInt 32 (-(Int.ofNat posScaled.toUInt64.toNat))

/-- Convert Q16.16 fixed-point to Float -/
def q16_16_to_float (x : Activation) : Float :=
  let xi := x.toInt
  Float.ofInt xi / Float.ofNat (2^16)

-- ============================================================================
-- Helpers
-- ============================================================================

def goldenDir : String := "Tests/golden-values"

/-- Check pass/fail against cosine threshold -/
def checkResult (name : String) (cosine : Float) (threshold : Float)
    (maxErr : Float) : IO Bool := do
  let passed := cosine >= threshold
  let tag := if passed then "PASS" else "FAIL"
  IO.println s!"  [{tag}] {name}"
  IO.println s!"    cosine similarity: {cosine} (threshold: {threshold})"
  IO.println s!"    max abs error:     {maxErr}"
  return passed

/-- Extract a slice of `dim` elements starting at token index `tok` -/
def tokenSlice (data : Array Float) (tok : Nat) (dim : Nat) : Array Float :=
  let start := tok * dim
  let stop := start + dim
  Id.run do
    let mut out := #[]
    for i in [start:stop] do
      out := out.push (data.getD i 0.0)
    return out

-- ============================================================================
-- Test 1: Q16.16 Round-Trip Fidelity
-- ============================================================================

def testQ16RoundTrip (golden : Array Float) : IO Bool := do
  IO.println "--- Test 1: Q16.16 Round-Trip Fidelity ---"
  IO.println s!"  Input size: {golden.size} float32 values"

  -- Clamp values to Q16.16 representable range [-32768, 32767.99998]
  -- Values outside this range would overflow; we skip them for round-trip
  let mut original : Array Float := #[]
  let mut roundTripped : Array Float := #[]
  let mut skipped := 0

  for v in golden do
    if v >= -32768.0 && v <= 32767.0 then
      let q := float_to_q16_16 v
      let back := q16_16_to_float q
      original := original.push v
      roundTripped := roundTripped.push back
    else
      skipped := skipped + 1

  if skipped > 0 then
    IO.println s!"  (skipped {skipped} values outside Q16.16 range)"

  let report := generateReport original roundTripped
  IO.println s!"  elements compared: {report.size}"
  checkResult "Q16.16 round-trip" report.cosineSimilarity 0.9999 report.maxAbsError

-- ============================================================================
-- Test 2: reluSquared on Golden Data
-- ============================================================================

def testReluSquared (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 2: reluSquared on Golden Data ---"

  let slice := tokenSlice golden 0 dim
  IO.println s!"  Input: token 0, dim={dim}, size={slice.size}"

  -- RTL path: float -> Q16.16 -> reluSquared -> float
  let mut rtlResults : Array Float := #[]
  -- Float reference: if x <= 0 then 0 else x*x
  let mut refResults : Array Float := #[]

  for v in slice do
    -- RTL path
    let q := float_to_q16_16 v
    let rq := reluSquared q
    rtlResults := rtlResults.push (q16_16_to_float rq)

    -- Float reference
    let refVal := if v <= 0.0 then 0.0 else v * v
    refResults := refResults.push refVal

  let report := generateReport refResults rtlResults
  checkResult "reluSquared" report.cosineSimilarity 0.999 report.maxAbsError

-- ============================================================================
-- Test 3: elemMul on Golden Data
-- ============================================================================

def testElemMul (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 3: elemMul on Golden Data ---"

  let sliceA := tokenSlice golden 0 dim
  let sliceB := tokenSlice golden 1 dim
  IO.println s!"  Input: token 0 * token 1, dim={dim}"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for i in [:dim] do
    let a := sliceA.getD i 0.0
    let b := sliceB.getD i 0.0

    -- RTL path
    let qa := float_to_q16_16 a
    let qb := float_to_q16_16 b
    let qr := elemMul qa qb
    rtlResults := rtlResults.push (q16_16_to_float qr)

    -- Float reference
    refResults := refResults.push (a * b)

  let report := generateReport refResults rtlResults
  checkResult "elemMul" report.cosineSimilarity 0.999 report.maxAbsError

-- ============================================================================
-- Test 4: residualAdd on Golden Data
-- ============================================================================

def testResidualAdd (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 4: residualAdd on Golden Data ---"

  let sliceA := tokenSlice golden 0 dim
  let sliceB := tokenSlice golden 1 dim
  IO.println s!"  Input: token 0 + token 1, dim={dim}"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for i in [:dim] do
    let a := sliceA.getD i 0.0
    let b := sliceB.getD i 0.0

    -- RTL path
    let qa := float_to_q16_16 a
    let qb := float_to_q16_16 b
    let qr := residualAdd qa qb
    rtlResults := rtlResults.push (q16_16_to_float qr)

    -- Float reference
    refResults := refResults.push (a + b)

  let report := generateReport refResults rtlResults
  checkResult "residualAdd" report.cosineSimilarity 0.9999 report.maxAbsError

-- ============================================================================
-- Test 5: fixedPointScale on Golden Data
-- ============================================================================

def testFixedPointScale (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 5: fixedPointScale on Golden Data ---"

  let slice := tokenSlice golden 0 dim
  IO.println s!"  Input: token 0, dim={dim}"

  -- Test 5a: identity scale (1.0 in Q8.24 = 0x01000000)
  IO.println "  5a: Scale by 1.0 (identity)"
  let unitScale : ScaleFactor := BitVec.ofNat 32 0x01000000

  let mut rtlIdentity : Array Float := #[]
  let mut refIdentity : Array Float := #[]

  for v in slice do
    let q := float_to_q16_16 v
    -- Convert Q16.16 to 48-bit accumulator (sign-extend)
    let acc := signExtend32to48 q
    let result := fixedPointScale acc unitScale
    rtlIdentity := rtlIdentity.push (q16_16_to_float result)
    refIdentity := refIdentity.push v

  let reportId := generateReport refIdentity rtlIdentity
  let passIdentity ← checkResult "fixedPointScale identity (1.0)"
    reportId.cosineSimilarity 0.9999 reportId.maxAbsError

  -- Test 5b: scale by 0.5 (Q8.24 = 0x00800000)
  IO.println "  5b: Scale by 0.5"
  let halfScale : ScaleFactor := BitVec.ofNat 32 0x00800000

  let mut rtlHalf : Array Float := #[]
  let mut refHalf : Array Float := #[]

  for v in slice do
    let q := float_to_q16_16 v
    let acc := signExtend32to48 q
    let result := fixedPointScale acc halfScale
    rtlHalf := rtlHalf.push (q16_16_to_float result)
    refHalf := refHalf.push (v * 0.5)

  let reportHalf := generateReport refHalf rtlHalf
  let passHalf ← checkResult "fixedPointScale half (0.5)"
    reportHalf.cosineSimilarity 0.9999 reportHalf.maxAbsError

  return passIdentity && passHalf

-- ============================================================================
-- Test 6: quantizeToInt8 on Golden Data
-- ============================================================================

def testQuantizeToInt8 (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 6: quantizeToInt8 on Golden Data ---"

  let slice := tokenSlice golden 0 dim
  let quantShift := 10
  IO.println s!"  Input: token 0, dim={dim}, quantShift={quantShift}"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for v in slice do
    -- RTL path
    let q := float_to_q16_16 v
    let qint8 := quantizeToInt8 q quantShift
    let int8Val := qint8.toInt
    rtlResults := rtlResults.push (Float.ofInt int8Val)

    -- Float reference: floor(x_q16_16 / 2^shift), clamped to [-128,127]
    -- We need to use the Q16.16 integer representation for the reference too,
    -- since quantizeToInt8 operates on the fixed-point integer
    let qi := q.toInt
    let shifted := qi / (2 ^ quantShift : Int)
    let clamped :=
      if shifted > 127 then 127
      else if shifted < -128 then -128
      else shifted
    refResults := refResults.push (Float.ofInt clamped)

  -- For quantization, we expect exact match since both paths do integer arithmetic
  let mut exactMatches := 0
  let mut total := 0
  for i in [:rtlResults.size] do
    total := total + 1
    if rtlResults.getD i 0.0 == refResults.getD i 0.0 then
      exactMatches := exactMatches + 1

  let allExact := exactMatches == total
  let tag := if allExact then "PASS" else "FAIL"
  IO.println s!"  [{tag}] quantizeToInt8: {exactMatches}/{total} exact matches"
  return allExact

-- ============================================================================
-- Test 7: Input Tokens Validation
-- ============================================================================

/-- Load UInt32 array from binary file (little-endian) -/
def loadUInt32ArrayFromFile (path : String) : IO (Array UInt32) := do
  let bytes ← IO.FS.readBinFile path
  let numInts := bytes.size / 4
  let mut result := #[]
  for i in [0:numInts] do
    let offset := i * 4
    if offset + 4 <= bytes.size then
      let b0 := bytes.get! offset |>.toUInt32
      let b1 := bytes.get! (offset + 1) |>.toUInt32
      let b2 := bytes.get! (offset + 2) |>.toUInt32
      let b3 := bytes.get! (offset + 3) |>.toUInt32
      let bits := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
      result := result.push bits
  return result

def testInputTokens : IO Bool := do
  IO.println "--- Test 7: Input Tokens Validation ---"

  let tokensPath := s!"{goldenDir}/input_tokens.bin"
  let tokens ← loadUInt32ArrayFromFile tokensPath

  -- Expected tokens from metadata.json: [128000, 9906, 1917]
  let expected : Array UInt32 := #[128000, 9906, 1917]

  IO.println s!"  Loaded: {tokens.size} token IDs"
  IO.println s!"  Expected: {expected.size} token IDs"

  let sizeOk := tokens.size == expected.size

  let mut allMatch := sizeOk
  for i in [:tokens.size.min expected.size] do
    let got := tokens.getD i 0
    let exp := expected.getD i 0
    let match_ := got == exp
    let tag := if match_ then "ok" else "MISMATCH"
    IO.println s!"  token[{i}]: got={got} expected={exp} [{tag}]"
    if !match_ then allMatch := false

  let tag := if allMatch then "PASS" else "FAIL"
  IO.println s!"  [{tag}] input_tokens.bin matches metadata"
  return allMatch

-- ============================================================================
-- Test 8: Logits Golden Data Statistics (stats only, no RTL)
-- ============================================================================

def testLogitsStats : IO Bool := do
  IO.println "--- Test 8: Logits Golden Data Statistics (stats only) ---"

  let logitsPath := s!"{goldenDir}/logits_output.bin"
  let logits ← loadFloatArrayFromFile logitsPath
  let expectedSize := 3 * 128256  -- 3 tokens × vocab_size

  IO.println s!"  Loaded: {logits.size} float32 values"
  IO.println s!"  Expected: {expectedSize} (3 x 128256)"

  let sizeOk := logits.size == expectedSize

  if logits.size > 0 then
    -- Compute basic statistics
    let mut minVal := logits[0]!
    let mut maxVal := logits[0]!
    let mut sum := 0.0
    for v in logits do
      if v < minVal then minVal := v
      if v > maxVal then maxVal := v
      sum := sum + v
    let meanVal := sum / logits.size.toFloat
    IO.println s!"  Min:  {minVal}"
    IO.println s!"  Max:  {maxVal}"
    IO.println s!"  Mean: {meanVal}"

  let tag := if sizeOk then "PASS" else "FAIL"
  IO.println s!"  [{tag}] logits size check"
  return sizeOk

-- ============================================================================
-- Test 9: reluSquared on Logits
-- ============================================================================

def testReluSquaredLogits (logits : Array Float) (vocabSize : Nat) : IO Bool := do
  IO.println "--- Test 9: reluSquared on Logits ---"

  let logitsSubsetSize := 4096
  let slice := tokenSlice logits 0 vocabSize
  let subset := slice.extract 0 logitsSubsetSize
  IO.println s!"  Input: first {subset.size} logits from token 0"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for v in subset do
    let q := float_to_q16_16 v
    let rq := reluSquared q
    rtlResults := rtlResults.push (q16_16_to_float rq)

    let refVal := if v <= 0.0 then 0.0 else v * v
    refResults := refResults.push refVal

  let report := generateReport refResults rtlResults
  checkResult "reluSquared (logits)" report.cosineSimilarity 0.999 report.maxAbsError

-- ============================================================================
-- Test 10: elemMul on Logits
-- ============================================================================

def testElemMulLogits (logits : Array Float) (vocabSize : Nat) : IO Bool := do
  IO.println "--- Test 10: elemMul on Logits ---"

  let logitsSubsetSize := 4096
  let sliceA := tokenSlice logits 0 vocabSize
  let sliceB := tokenSlice logits 1 vocabSize
  let subsetA := sliceA.extract 0 logitsSubsetSize
  let subsetB := sliceB.extract 0 logitsSubsetSize
  IO.println s!"  Input: first {subsetA.size} logits, token 0 * token 1"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for i in [:logitsSubsetSize] do
    let a := subsetA.getD i 0.0
    let b := subsetB.getD i 0.0

    let qa := float_to_q16_16 a
    let qb := float_to_q16_16 b
    let qr := elemMul qa qb
    rtlResults := rtlResults.push (q16_16_to_float qr)

    refResults := refResults.push (a * b)

  let report := generateReport refResults rtlResults
  checkResult "elemMul (logits)" report.cosineSimilarity 0.999 report.maxAbsError

-- ============================================================================
-- Test 11: residualAdd on Logits
-- ============================================================================

def testResidualAddLogits (logits : Array Float) (vocabSize : Nat) : IO Bool := do
  IO.println "--- Test 11: residualAdd on Logits ---"

  let logitsSubsetSize := 4096
  let sliceA := tokenSlice logits 0 vocabSize
  let sliceB := tokenSlice logits 1 vocabSize
  let subsetA := sliceA.extract 0 logitsSubsetSize
  let subsetB := sliceB.extract 0 logitsSubsetSize
  IO.println s!"  Input: first {subsetA.size} logits, token 0 + token 1"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for i in [:logitsSubsetSize] do
    let a := subsetA.getD i 0.0
    let b := subsetB.getD i 0.0

    let qa := float_to_q16_16 a
    let qb := float_to_q16_16 b
    let qr := residualAdd qa qb
    rtlResults := rtlResults.push (q16_16_to_float qr)

    refResults := refResults.push (a + b)

  let report := generateReport refResults rtlResults
  checkResult "residualAdd (logits)" report.cosineSimilarity 0.9999 report.maxAbsError

-- ============================================================================
-- Test 12: quantizeToInt8 on Logits
-- ============================================================================

def testQuantizeToInt8Logits (logits : Array Float) (vocabSize : Nat) : IO Bool := do
  IO.println "--- Test 12: quantizeToInt8 on Logits ---"

  let logitsSubsetSize := 4096
  let quantShift := 10
  let slice := tokenSlice logits 0 vocabSize
  let subset := slice.extract 0 logitsSubsetSize
  IO.println s!"  Input: first {subset.size} logits from token 0, quantShift={quantShift}"

  let mut rtlResults : Array Float := #[]
  let mut refResults : Array Float := #[]

  for v in subset do
    let q := float_to_q16_16 v
    let qint8 := quantizeToInt8 q quantShift
    let int8Val := qint8.toInt
    rtlResults := rtlResults.push (Float.ofInt int8Val)

    let qi := q.toInt
    let shifted := qi / (2 ^ quantShift : Int)
    let clamped :=
      if shifted > 127 then 127
      else if shifted < -128 then -128
      else shifted
    refResults := refResults.push (Float.ofInt clamped)

  let mut exactMatches := 0
  let mut total := 0
  for i in [:rtlResults.size] do
    total := total + 1
    if rtlResults.getD i 0.0 == refResults.getD i 0.0 then
      exactMatches := exactMatches + 1

  let allExact := exactMatches == total
  let tag := if allExact then "PASS" else "FAIL"
  IO.println s!"  [{tag}] quantizeToInt8 (logits): {exactMatches}/{total} exact matches"
  return allExact

-- ============================================================================
-- FFN Forward Pass Helpers (copied from Tests/Equivalence.lean to avoid
-- importing native_decide theorems that slow compilation)
-- ============================================================================

/-- Ternary dot product for arbitrary-dimension Int weight arrays. -/
def ternaryDotSmall (weights : Array Int) (activations : Array Activation) : Accumulator :=
  Id.run do
    let n := min weights.size activations.size
    let mut acc : Int := 0
    for i in [:n] do
      acc := acc + weights[i]! * (activations[i]!).toInt
    return BitVec.ofInt accBits acc

/-- Single BitLinear forward: dot product → scale -/
def bitLinearForward (weights : Array Int) (scale : ScaleFactor)
    (activations : Array Activation) : Activation :=
  fixedPointScale (ternaryDotSmall weights activations) scale

/-- FFN forward for one output element (scalar pipeline):
    gate branch: dot → scale → ReLU²
    up branch: dot → scale
    mix: elemMul(gate_relu, up_scaled)
    down: dot(downW, [mixed]) → scale
    residual: input[0] + down -/
def ffnForwardScalar (input : Array Activation)
    (gateW upW downW : Array Int)
    (gateScale upScale downScale : ScaleFactor) : Activation :=
  let gateOut := bitLinearForward gateW gateScale input
  let gateRelu := reluSquared gateOut
  let upOut := bitLinearForward upW upScale input
  let mixed := elemMul gateRelu upOut
  let downOut := bitLinearForward downW downScale #[mixed]
  residualAdd input[0]! downOut

-- ============================================================================
-- Test 13: FFN Forward Pass (Toy Model, Exact Match)
-- ============================================================================

def testFFNForwardToy : IO Bool := do
  IO.println "--- Test 13: FFN Forward Pass (Toy Model, Exact Match) ---"

  -- Layer 0: input [2.0, 1.0, 3.0, 1.0], all scales=1.0
  let unitScale : ScaleFactor := BitVec.ofNat 32 0x01000000  -- 1.0 in Q8.24
  let input0 : Array Activation := #[
    BitVec.ofNat 32 0x20000,  -- 2.0
    BitVec.ofNat 32 0x10000,  -- 1.0
    BitVec.ofNat 32 0x30000,  -- 3.0
    BitVec.ofNat 32 0x10000   -- 1.0
  ]
  let gateW0 : Array Int := #[1, -1, 0, 1]
  let upW0 : Array Int := #[-1, 1, 1, 0]
  let downW0 : Array Int := #[1, 0, -1, 1]

  let result0 := ffnForwardScalar input0 gateW0 upW0 downW0 unitScale unitScale unitScale
  let expected0 : Activation := BitVec.ofNat 32 0xA0000  -- 10.0 in Q16.16
  let pass0 := result0 == expected0

  IO.println s!"  Layer 0: input=[2.0, 1.0, 3.0, 1.0]"
  IO.println s!"    gate=[1,-1,0,1] up=[-1,1,1,0] down=[1,0,-1,1] scales=1.0"
  IO.println s!"    result = {q16_16_to_float result0} (Q16.16 = 0x{String.ofList (Nat.toDigits 16 result0.toNat)})"
  IO.println s!"    expected = 10.0 (Q16.16 = 0xA0000)"
  let tag0 := if pass0 then "PASS" else "FAIL"
  IO.println s!"  [{tag0}] Layer 0 exact match"

  -- Layer 1: input [1.0, 4.0, 1.0, 1.0]
  -- gate=[0,1,-1,-1] scale=0.5, up=[1,0,0,1] scale=1.0, down=[-1,1,1,0] scale=0.75
  let halfScale : ScaleFactor := BitVec.ofNat 32 0x00800000   -- 0.5 in Q8.24
  let threeQtrScale : ScaleFactor := BitVec.ofNat 32 0x00C00000  -- 0.75 in Q8.24
  let input1 : Array Activation := #[
    BitVec.ofNat 32 0x10000,  -- 1.0
    BitVec.ofNat 32 0x40000,  -- 4.0
    BitVec.ofNat 32 0x10000,  -- 1.0
    BitVec.ofNat 32 0x10000   -- 1.0
  ]
  let gateW1 : Array Int := #[0, 1, -1, -1]
  let upW1 : Array Int := #[1, 0, 0, 1]
  let downW1 : Array Int := #[-1, 1, 1, 0]

  let result1 := ffnForwardScalar input1 gateW1 upW1 downW1 halfScale unitScale threeQtrScale
  let expected1 : Activation := BitVec.ofInt 32 (-0x8000)  -- -0.5 in Q16.16
  let pass1 := result1 == expected1

  IO.println s!"  Layer 1: input=[1.0, 4.0, 1.0, 1.0]"
  IO.println s!"    gate=[0,1,-1,-1] scale=0.5, up=[1,0,0,1] scale=1.0, down=[-1,1,1,0] scale=0.75"
  IO.println s!"    result = {q16_16_to_float result1} (Q16.16 = {result1.toInt})"
  IO.println s!"    expected = -0.5 (Q16.16 = -32768)"
  let tag1 := if pass1 then "PASS" else "FAIL"
  IO.println s!"  [{tag1}] Layer 1 exact match"

  return pass0 && pass1

-- ============================================================================
-- Test 14: FFN Forward on Golden Hidden States
-- ============================================================================

def testFFNForwardGolden (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 14: FFN Forward on Golden Hidden States ---"

  -- Extract first 4 elements of token 0
  let slice := tokenSlice golden 0 dim
  let n := 4
  IO.println s!"  Input: first {n} elements of token 0 from final_norm_output"

  -- Convert to Q16.16
  let mut inputQ : Array Activation := #[]
  let mut inputF : Array Float := #[]
  for i in [:n] do
    let v := slice.getD i 0.0
    inputQ := inputQ.push (float_to_q16_16 v)
    inputF := inputF.push v

  IO.println s!"  Float values: {inputF}"

  -- Use same toy weights as Test 13 Layer 0
  let unitScale : ScaleFactor := BitVec.ofNat 32 0x01000000
  let gateW : Array Int := #[1, -1, 0, 1]
  let upW : Array Int := #[-1, 1, 1, 0]
  let downW : Array Int := #[1, 0, -1, 1]

  -- RTL path
  let rtlResult := ffnForwardScalar inputQ gateW upW downW unitScale unitScale unitScale
  let rtlFloat := q16_16_to_float rtlResult

  -- Float reference: manually compute the same pipeline
  -- gate_dot = 1*x[0] + (-1)*x[1] + 0*x[2] + 1*x[3]
  let gateDot := inputF.getD 0 0.0 - inputF.getD 1 0.0 + inputF.getD 3 0.0
  -- gate_scaled = gateDot * 1.0
  let gateScaled := gateDot
  -- gate_relu = relu²(gateScaled)
  let gateRelu := if gateScaled <= 0.0 then 0.0 else gateScaled * gateScaled
  -- up_dot = (-1)*x[0] + 1*x[1] + 1*x[2] + 0*x[3]
  let upDot := -inputF.getD 0 0.0 + inputF.getD 1 0.0 + inputF.getD 2 0.0
  let upScaled := upDot
  -- mixed = gateRelu * upScaled
  let mixed := gateRelu * upScaled
  -- down_dot = 1*mixed + 0 + (-1)*0 + 1*0 = mixed (only 1 element)
  let downDot := mixed
  let downScaled := downDot
  -- residual = x[0] + downScaled
  let refFloat := inputF.getD 0 0.0 + downScaled

  IO.println s!"  RTL result:   {rtlFloat}"
  IO.println s!"  Float ref:    {refFloat}"

  -- Compute cosine between single values (use arrays of size 1)
  let report := generateReport #[refFloat] #[rtlFloat]
  checkResult "FFN forward on golden data" report.cosineSimilarity 0.999 report.maxAbsError

-- ============================================================================
-- Test 15: Attention Score Pipeline on Golden Data
-- ============================================================================

def testAttentionScorePipeline (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 15: Attention Score Pipeline on Golden Data ---"

  -- Use first 64 elements of token 0 and token 1
  let n := 64
  let quantShift := 10
  let scaleDkShift := 3  -- 1/sqrt(d_k) approximation via shift

  let slice0 := tokenSlice golden 0 dim
  let slice1 := tokenSlice golden 1 dim
  IO.println s!"  Input: first {n} elements of token 0 (Q) and token 1 (K)"

  -- Convert to Q16.16, then quantize to INT8
  let mut qArr : Array QActivation := #[]
  let mut kArr : Array QActivation := #[]
  let mut qFloats : Array Float := #[]
  let mut kFloats : Array Float := #[]

  for i in [:n] do
    let v0 := slice0.getD i 0.0
    let v1 := slice1.getD i 0.0
    let q16_0 := float_to_q16_16 v0
    let q16_1 := float_to_q16_16 v1
    let qi := quantizeToInt8 q16_0 quantShift
    let ki := quantizeToInt8 q16_1 quantShift
    qArr := qArr.push qi
    kArr := kArr.push ki
    qFloats := qFloats.push (Float.ofInt qi.toInt)
    kFloats := kFloats.push (Float.ofInt ki.toInt)

  -- RTL path: int8DotProduct and scaledScore
  let rawDot := int8DotProduct qArr kArr
  let scaled := scaledScore qArr kArr scaleDkShift

  -- Float reference: compute same operations in float
  let mut floatDot : Float := 0.0
  for i in [:n] do
    floatDot := floatDot + qFloats.getD i 0.0 * kFloats.getD i 0.0
  let floatScaled := Float.floor (floatDot / Float.ofNat (2 ^ scaleDkShift))

  IO.println s!"  Raw dot product (RTL):  {rawDot}"
  IO.println s!"  Raw dot product (float): {floatDot}"
  IO.println s!"  Scaled score (RTL):      {scaled}"
  IO.println s!"  Scaled score (float):    {floatScaled}"

  -- Both should be exact since all operations are integer arithmetic after quantization
  let dotMatch := Float.ofInt rawDot == floatDot
  let scaledMatch := Float.ofInt scaled == floatScaled

  let allPass := dotMatch && scaledMatch
  let tag := if allPass then "PASS" else "FAIL"
  IO.println s!"  [{tag}] Attention score pipeline"
  IO.println s!"    dot match:    {dotMatch}"
  IO.println s!"    scaled match: {scaledMatch}"
  return allPass

-- ============================================================================
-- Test 16: Softmax + Weighted V Sum on Golden Data
-- ============================================================================

def testSoftmaxWeightedVSum (golden : Array Float) (dim : Nat) : IO Bool := do
  IO.println "--- Test 16: Softmax + Weighted V Sum on Golden Data ---"

  let n := 64  -- elements for Q/K vectors
  let vDim := 8  -- V matrix columns
  let numTokens := 3
  let quantShift := 10
  let scaleDkShift := 3

  IO.println s!"  Computing {numTokens} attention scores (first {n} elements vs token 0)"

  -- Step 1: Compute attention scores for each token vs token 0
  let slice0 := tokenSlice golden 0 dim
  let mut scores : Array Int := #[]

  for t in [:numTokens] do
    let sliceT := tokenSlice golden t dim
    -- Quantize both to INT8
    let mut qArr : Array QActivation := #[]
    let mut kArr : Array QActivation := #[]
    for i in [:n] do
      let v0 := slice0.getD i 0.0
      let vT := sliceT.getD i 0.0
      qArr := qArr.push (quantizeToInt8 (float_to_q16_16 v0) quantShift)
      kArr := kArr.push (quantizeToInt8 (float_to_q16_16 vT) quantShift)
    let s := scaledScore qArr kArr scaleDkShift
    scores := scores.push s
    IO.println s!"    Score[{t}] = {s}"

  -- Step 2: Softmax
  let weights := softmaxRef scores
  IO.println s!"  Softmax weights: {weights}"

  -- Step 3: Build V matrix (first vDim elements of each token, quantized to INT8 values as Int)
  let mut vMatrix : Array (Array Int) := #[]
  for t in [:numTokens] do
    let sliceT := tokenSlice golden t dim
    let mut row : Array Int := #[]
    for j in [:vDim] do
      let v := sliceT.getD j 0.0
      let qi := quantizeToInt8 (float_to_q16_16 v) quantShift
      row := row.push qi.toInt
    vMatrix := vMatrix.push row

  -- Step 4: Compute weighted V sum
  let mut output : Array Int := #[]
  for j in [:vDim] do
    let val := weightedVSum weights vMatrix j
    output := output.push val

  IO.println s!"  Weighted V sum output: {output}"

  -- Validation checks
  -- Check 1: Softmax weights sum ≈ 2^24 (±1%)
  let mut weightSum : Int := 0
  for w in weights do
    weightSum := weightSum + w
  let expectedSum : Int := 2 ^ 24  -- 16777216
  let tolerance := expectedSum / 100  -- 1%
  let sumOk := (weightSum - expectedSum).natAbs < tolerance.natAbs
  IO.println s!"  Weight sum: {weightSum} (expected ≈ {expectedSum}, tolerance ±{tolerance})"
  let tagSum := if sumOk then "ok" else "FAIL"
  IO.println s!"    [{tagSum}] Weight sum within 1%"

  -- Check 2: Each weight in [0, 2^24]
  let mut rangeOk := true
  for i in [:weights.size] do
    let w := weights.getD i 0
    if w < 0 || w > expectedSum then
      IO.println s!"    FAIL: weight[{i}] = {w} out of range"
      rangeOk := false
  let tagRange := if rangeOk then "ok" else "FAIL"
  IO.println s!"    [{tagRange}] All weights in [0, 2^24]"

  -- Check 3: Output is bounded (sanity check — each output should be within INT8 range × some factor)
  let mut outputBounded := true
  for j in [:output.size] do
    let v := output.getD j 0
    -- Each output is weighted sum of INT8 values with Q8.24 weights summing to ~1.0
    -- So output should be roughly in INT8 range [-128, 127]
    if v < -256 || v > 256 then
      IO.println s!"    WARNING: output[{j}] = {v} (unusually large)"
      outputBounded := false
  let tagBound := if outputBounded then "ok" else "WARN"
  IO.println s!"    [{tagBound}] Output values bounded"

  let allPass := sumOk && rangeOk
  let tag := if allPass then "PASS" else "FAIL"
  IO.println s!"  [{tag}] Softmax + weighted V sum"
  return allPass

-- ============================================================================
-- Main
-- ============================================================================

def runAll : IO Unit := do
  IO.println "=== RTL Golden Value Validation ==="
  IO.println s!"  Golden data dir: {goldenDir}"
  IO.println ""

  -- Load golden data
  let normPath := s!"{goldenDir}/final_norm_output.bin"
  IO.println s!"Loading {normPath}..."
  let golden ← loadFloatArrayFromFile normPath
  let dim := 2560  -- from metadata.json: hidden_dim
  IO.println s!"  Loaded {golden.size} values ({golden.size / dim} tokens x {dim} dim)"
  IO.println ""

  let mut allPassed := true

  -- Test 1: Q16.16 round-trip
  let p1 ← testQ16RoundTrip golden
  allPassed := allPassed && p1
  IO.println ""

  -- Test 2: reluSquared
  let p2 ← testReluSquared golden dim
  allPassed := allPassed && p2
  IO.println ""

  -- Test 3: elemMul
  let p3 ← testElemMul golden dim
  allPassed := allPassed && p3
  IO.println ""

  -- Test 4: residualAdd
  let p4 ← testResidualAdd golden dim
  allPassed := allPassed && p4
  IO.println ""

  -- Test 5: fixedPointScale
  let p5 ← testFixedPointScale golden dim
  allPassed := allPassed && p5
  IO.println ""

  -- Test 6: quantizeToInt8
  let p6 ← testQuantizeToInt8 golden dim
  allPassed := allPassed && p6
  IO.println ""

  -- Test 7: input tokens validation
  let p7 ← testInputTokens
  allPassed := allPassed && p7
  IO.println ""

  -- Test 8: logits stats
  let p8 ← testLogitsStats
  allPassed := allPassed && p8
  IO.println ""

  -- Load logits data for tests 9-12
  let logitsPath := s!"{goldenDir}/logits_output.bin"
  IO.println s!"Loading {logitsPath} for logits tests..."
  let logits ← loadFloatArrayFromFile logitsPath
  let vocabSize := 128256
  IO.println s!"  Loaded {logits.size} values ({logits.size / vocabSize} tokens x {vocabSize} vocab)"
  IO.println ""

  -- Test 9: reluSquared on logits
  let p9 ← testReluSquaredLogits logits vocabSize
  allPassed := allPassed && p9
  IO.println ""

  -- Test 10: elemMul on logits
  let p10 ← testElemMulLogits logits vocabSize
  allPassed := allPassed && p10
  IO.println ""

  -- Test 11: residualAdd on logits
  let p11 ← testResidualAddLogits logits vocabSize
  allPassed := allPassed && p11
  IO.println ""

  -- Test 12: quantizeToInt8 on logits
  let p12 ← testQuantizeToInt8Logits logits vocabSize
  allPassed := allPassed && p12
  IO.println ""

  -- Test 13: FFN Forward Pass (Toy Model, Exact Match)
  let p13 ← testFFNForwardToy
  allPassed := allPassed && p13
  IO.println ""

  -- Test 14: FFN Forward on Golden Hidden States
  let p14 ← testFFNForwardGolden golden dim
  allPassed := allPassed && p14
  IO.println ""

  -- Test 15: Attention Score Pipeline on Golden Data
  let p15 ← testAttentionScorePipeline golden dim
  allPassed := allPassed && p15
  IO.println ""

  -- Test 16: Softmax + Weighted V Sum on Golden Data
  let p16 ← testSoftmaxWeightedVSum golden dim
  allPassed := allPassed && p16
  IO.println ""

  IO.println "==========================================="
  if allPassed then
    IO.println "ALL TESTS PASSED"
  else
    IO.println "SOME TESTS FAILED"

end Sparkle.Examples.BitNet.Tests.RTLGoldenValidation
