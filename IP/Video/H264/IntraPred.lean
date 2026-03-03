/-
  H.264 Intra_4×4 Prediction

  Implements 4 main prediction modes (of 9 total):
  - Mode 0: Vertical (copy above row)
  - Mode 1: Horizontal (copy left column)
  - Mode 2: DC (average of neighbors)
  - Mode 3: Diagonal Down-Left

  Neighbor layout:
    M A B C D E F G H   (above[0..7], aboveLeft)
    I x x x x           (left[0..3])
    J x x x x
    K x x x x
    L x x x x

  Reference: ITU-T H.264 Section 8.3.1.2
-/

import Sparkle

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.Video.H264.IntraPred

-- ============================================================================
-- Types
-- ============================================================================

/-- Neighbor pixels for a 4×4 block prediction -/
structure Neighbors where
  above     : Array Nat  -- 8 pixels: A(0)-H(7)
  left      : Array Nat  -- 4 pixels: I(0)-L(3)
  aboveLeft : Nat        -- M pixel
  hasAbove  : Bool
  hasLeft   : Bool
  deriving Repr

/-- 4×4 block as flat array of 16 values -/
abbrev Block4x4 := Array Nat

-- ============================================================================
-- Prediction modes (pure functions)
-- ============================================================================

/-- Mode 0: Vertical — copy above pixels to each row -/
def predictVertical (n : Neighbors) : Block4x4 := Id.run do
  let mut pred := Array.replicate 16 0
  for i in [:4] do
    for j in [:4] do
      if h : j < n.above.size then
        pred := pred.set! (i * 4 + j) n.above[j]
  pred

/-- Mode 1: Horizontal — copy left pixels to each column -/
def predictHorizontal (n : Neighbors) : Block4x4 := Id.run do
  let mut pred := Array.replicate 16 0
  for i in [:4] do
    for j in [:4] do
      if h : i < n.left.size then
        pred := pred.set! (i * 4 + j) n.left[i]
  pred

/-- Mode 2: DC — average of available neighbors -/
def predictDC (n : Neighbors) : Block4x4 :=
  let (sum, count) := Id.run do
    let mut s := 0
    let mut c := 0
    if n.hasAbove then
      for j in [:4] do
        if h : j < n.above.size then
          s := s + n.above[j]
          c := c + 1
    if n.hasLeft then
      for i in [:4] do
        if h : i < n.left.size then
          s := s + n.left[i]
          c := c + 1
    (s, c)
  let dc := if count > 0 then (sum + count / 2) / count else 128
  Array.replicate 16 dc

/-- Mode 3: Diagonal Down-Left -/
def predictDiagDownLeft (n : Neighbors) : Block4x4 := Id.run do
  let get := fun (idx : Nat) =>
    if h : idx < n.above.size then n.above[idx] else 0
  let a := get 0; let b := get 1; let c := get 2; let d := get 3
  let e := get 4; let f := get 5; let g := get 6; let h := get 7

  let mut pred := Array.replicate 16 0

  -- Using H.264 spec filtering: (x + 2*y + z + 2) >> 2
  pred := pred.set! 0  ((a + 2*b + c + 2) / 4)
  pred := pred.set! 1  ((b + 2*c + d + 2) / 4)
  pred := pred.set! 4  ((b + 2*c + d + 2) / 4)
  pred := pred.set! 2  ((c + 2*d + e + 2) / 4)
  pred := pred.set! 5  ((c + 2*d + e + 2) / 4)
  pred := pred.set! 8  ((c + 2*d + e + 2) / 4)
  pred := pred.set! 3  ((d + 2*e + f + 2) / 4)
  pred := pred.set! 6  ((d + 2*e + f + 2) / 4)
  pred := pred.set! 9  ((d + 2*e + f + 2) / 4)
  pred := pred.set! 12 ((d + 2*e + f + 2) / 4)
  pred := pred.set! 7  ((e + 2*f + g + 2) / 4)
  pred := pred.set! 10 ((e + 2*f + g + 2) / 4)
  pred := pred.set! 13 ((e + 2*f + g + 2) / 4)
  pred := pred.set! 11 ((f + 2*g + h + 2) / 4)
  pred := pred.set! 14 ((f + 2*g + h + 2) / 4)
  pred := pred.set! 15 ((g + 2*h + h + 2) / 4)

  pred

/-- Predict a 4×4 block using the specified mode (0-3 supported) -/
def predict (mode : Nat) (n : Neighbors) : Block4x4 :=
  match mode with
  | 0 => predictVertical n
  | 1 => predictHorizontal n
  | 2 => predictDC n
  | 3 => predictDiagDownLeft n
  | _ => Array.replicate 16 128  -- unsupported mode fallback

-- ============================================================================
-- Residual computation
-- ============================================================================

/-- Compute residual: original - predicted (signed) -/
def computeResidual (original predicted : Block4x4) : Array Int := Id.run do
  let mut res := Array.replicate 16 (0 : Int)
  for i in [:16] do
    let o := if h : i < original.size then original[i] else 0
    let p := if h : i < predicted.size then predicted[i] else 0
    res := res.set! i (Int.ofNat o - Int.ofNat p)
  res

/-- Reconstruct: predicted + decoded_residual, clamped to [0, 255] -/
def reconstruct (predicted : Block4x4) (residual : Array Int) : Block4x4 := Id.run do
  let mut result := Array.replicate 16 0
  for i in [:16] do
    let p := if h : i < predicted.size then predicted[i] else 0
    let r := if h : i < residual.size then residual[i] else 0
    let val := Int.ofNat p + r
    let clamped := if val < 0 then 0 else if val > 255 then 255 else val.toNat
    result := result.set! i clamped
  result

-- ============================================================================
-- Mode decision (SAD-based)
-- ============================================================================

/-- Sum of Absolute Differences between original and predicted blocks -/
def computeSAD (original predicted : Block4x4) : Nat := Id.run do
  let mut sad := 0
  for i in [:16] do
    let o := if h : i < original.size then original[i] else 0
    let p := if h : i < predicted.size then predicted[i] else 0
    sad := sad + (if o >= p then o - p else p - o)
  sad

/-- Choose best prediction mode (0-3) based on SAD -/
def bestMode (original : Block4x4) (n : Neighbors) : Nat := Id.run do
  let mut bestM := 0
  let mut bestSAD := computeSAD original (predict 0 n)
  for m in [1, 2, 3] do
    let sad := computeSAD original (predict m n)
    if sad < bestSAD then
      bestM := m
      bestSAD := sad
  bestM

-- ============================================================================
-- Golden value verification
-- ============================================================================

private def testNeighbors : Neighbors :=
  { above := #[10, 20, 30, 40, 50, 60, 70, 80]
  , left := #[15, 25, 35, 45]
  , aboveLeft := 5
  , hasAbove := true
  , hasLeft := true }

private def goldenVertical : Block4x4 :=
  #[10, 20, 30, 40, 10, 20, 30, 40, 10, 20, 30, 40, 10, 20, 30, 40]

private def goldenHorizontal : Block4x4 :=
  #[15, 15, 15, 15, 25, 25, 25, 25, 35, 35, 35, 35, 45, 45, 45, 45]

private def goldenDC : Block4x4 :=
  #[28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28]

private def goldenDDL : Block4x4 :=
  #[20, 30, 40, 50, 30, 40, 50, 60, 40, 50, 60, 70, 50, 60, 70, 78]

#eval do
  IO.println s!"Vertical:   {predict 0 testNeighbors == goldenVertical}"
  IO.println s!"Horizontal: {predict 1 testNeighbors == goldenHorizontal}"
  IO.println s!"DC:         {predict 2 testNeighbors == goldenDC}"
  IO.println s!"DDL:        {predict 3 testNeighbors == goldenDDL}"

end Sparkle.IP.Video.H264.IntraPred
