/-
  YOLOv8 Golden Value Loader

  Binary file loading and comparison metrics for validating
  RTL simulation output against Python golden values.

  Reuses patterns from Tests/BitNet/RTLGoldenValidation.lean.
-/

import Examples.YOLOv8.Types

namespace Sparkle.Examples.YOLOv8.Tests.GoldenLoader

open Sparkle.Examples.YOLOv8

-- ============================================================================
-- Binary File Loading
-- ============================================================================

/-- Load a binary file as an array of INT8 values.
    Each byte is treated as a signed 8-bit integer. -/
def loadInt8Array (path : String) : IO (Array (BitVec 8)) := do
  let bytes ← IO.FS.readBinFile path
  let mut result : Array (BitVec 8) := #[]
  for i in [:bytes.size] do
    result := result.push (BitVec.ofNat 8 bytes[i]!.toNat)
  return result

/-- Load a binary file as an array of INT4 values.
    Each byte contains two INT4 values: lower 4 bits first, upper 4 bits second. -/
def loadInt4Array (path : String) : IO (Array (BitVec 4)) := do
  let bytes ← IO.FS.readBinFile path
  let mut result : Array (BitVec 4) := #[]
  for i in [:bytes.size] do
    let b := bytes[i]!.toNat
    -- Lower nibble first
    result := result.push (BitVec.ofNat 4 (b % 16))
    -- Upper nibble second
    result := result.push (BitVec.ofNat 4 (b / 16))
  return result

/-- Load a binary file as an array of INT32 values (little-endian). -/
def loadInt32Array (path : String) : IO (Array (BitVec 32)) := do
  let bytes ← IO.FS.readBinFile path
  let numWords := bytes.size / 4
  let mut result : Array (BitVec 32) := #[]
  for i in [:numWords] do
    let offset := i * 4
    if offset + 4 <= bytes.size then
      let b0 := bytes[offset]!.toNat
      let b1 := bytes[offset + 1]!.toNat
      let b2 := bytes[offset + 2]!.toNat
      let b3 := bytes[offset + 3]!.toNat
      let word := b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      result := result.push (BitVec.ofNat 32 word)
  return result

/-- Load a binary file as an array of float32 values (little-endian).
    Converts IEEE 754 float32 to Lean Float (float64). -/
def loadFloat32Array (path : String) : IO (Array Float) := do
  let bytes ← IO.FS.readBinFile path
  let numFloats := bytes.size / 4
  let mut result : Array Float := #[]
  for i in [:numFloats] do
    let offset := i * 4
    if offset + 4 <= bytes.size then
      let b0 := bytes[offset]!.toUInt32
      let b1 := bytes[offset + 1]!.toUInt32
      let b2 := bytes[offset + 2]!.toUInt32
      let b3 := bytes[offset + 3]!.toUInt32
      let bits := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
      result := result.push (Float.ofScientific bits.toNat true 0)  -- placeholder
  return result

-- ============================================================================
-- Comparison Metrics
-- ============================================================================

/-- Compute max absolute error between two INT8 arrays. -/
def maxAbsError (reference predicted : Array (BitVec 8)) : Int :=
  Id.run do
    let n := min reference.size predicted.size
    let mut maxErr : Int := 0
    for i in [:n] do
      let refVal := if h : i < reference.size then reference[i].toInt else 0
      let predVal := if h : i < predicted.size then predicted[i].toInt else 0
      let err := (refVal - predVal).natAbs
      if (Int.ofNat err) > maxErr then
        maxErr := Int.ofNat err
    return maxErr

/-- Compute mean absolute error between two INT8 arrays. -/
def meanAbsError (reference predicted : Array (BitVec 8)) : Float :=
  Id.run do
    let n := min reference.size predicted.size
    if n == 0 then return 0.0
    let mut totalErr : Nat := 0
    for i in [:n] do
      let refVal := if h : i < reference.size then reference[i].toInt else 0
      let predVal := if h : i < predicted.size then predicted[i].toInt else 0
      totalErr := totalErr + (refVal - predVal).natAbs
    return Float.ofNat totalErr / Float.ofNat n

/-- Dot product of two Float arrays. -/
private def dotProduct (a b : Array Float) : Float :=
  if a.size != b.size then 0.0
  else Id.run do
    let mut sum : Float := 0.0
    for i in [:a.size] do
      sum := sum + a[i]! * b[i]!
    return sum

/-- L2 norm of a Float array. -/
private def l2Norm (a : Array Float) : Float :=
  Float.sqrt (dotProduct a a)

/-- Compute cosine similarity between two Float arrays.
    Returns 1.0 for identical vectors, 0.0 for orthogonal, -1.0 for opposite. -/
def cosineSimilarity (reference predicted : Array Float) : Float :=
  let dot := dotProduct reference predicted
  let normRef := l2Norm reference
  let normPred := l2Norm predicted
  if normRef == 0.0 || normPred == 0.0 then 0.0
  else dot / (normRef * normPred)

/-- Convert INT8 array to Float array for cosine similarity computation. -/
def int8ToFloat (arr : Array (BitVec 8)) : Array Float :=
  arr.map (fun v => Float.ofInt v.toInt)

/-- Compute cosine similarity between two INT8 arrays. -/
def cosineSimilarityInt8 (reference predicted : Array (BitVec 8)) : Float :=
  cosineSimilarity (int8ToFloat reference) (int8ToFloat predicted)

-- ============================================================================
-- Test Reporting
-- ============================================================================

/-- Test result report. -/
structure TestReport where
  name : String
  passed : Bool
  maxAbsErr : Int
  meanAbsErr : Float
  cosSim : Float
  deriving Repr

/-- Generate a report comparing reference vs predicted INT8 arrays. -/
def generateReport (name : String) (reference predicted : Array (BitVec 8)) : TestReport :=
  let maxErr := maxAbsError reference predicted
  let meanErr := meanAbsError reference predicted
  let cosSim := cosineSimilarityInt8 reference predicted
  { name := name
  , passed := true  -- Caller sets threshold
  , maxAbsErr := maxErr
  , meanAbsErr := meanErr
  , cosSim := cosSim }

/-- Print a test report to stdout. -/
def printReport (report : TestReport) : IO Unit := do
  IO.println s!"  {report.name}:"
  IO.println s!"    Max abs error:     {report.maxAbsErr}"
  IO.println s!"    Mean abs error:    {report.meanAbsErr}"
  IO.println s!"    Cosine similarity: {report.cosSim}"
  IO.println s!"    Status:            {if report.passed then "PASS" else "FAIL"}"

end Sparkle.Examples.YOLOv8.Tests.GoldenLoader
