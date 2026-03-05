/-
  H.264 Quantization / Dequantization

  Forward quantization:
    level = (|coeff| * MF[qp%6][pos_class] + f) >> qbits
    where qbits = 15 + floor(qp/6), f = 2^qbits / 3 (intra)

  Inverse dequantization:
    coeff' = level * V[qp%6][pos_class] * 2^floor(qp/6)

  Tables from H.264 spec Table 8-12, 8-13.

  Reference: ITU-T H.264 Section 8.5.11 (quant), 8.5.12 (dequant)
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.Video.H264.Quant

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- ============================================================================
-- Quantization tables (H.264 spec)
-- ============================================================================

/-- MF table: multiplication factor for quantization.
    Indexed by [qp%6][position_class].
    position_class: 0 = corner positions (0,0),(2,0),(0,2),(2,2)
                    1 = other even-even positions
                    2 = mixed even-odd positions -/
private def mfTable : Array (Array Nat) := #[
  #[13107, 5243, 8066],
  #[11916, 4660, 7490],
  #[10082, 4194, 6554],
  #[ 9362, 3647, 5825],
  #[ 8192, 3355, 5243],
  #[ 7282, 2893, 4559]
]

/-- V table: scaling factor for dequantization.
    Indexed by [qp%6][position_class]. -/
private def vTable : Array (Array Nat) := #[
  #[10, 16, 13],
  #[11, 18, 14],
  #[13, 20, 16],
  #[14, 23, 18],
  #[16, 25, 20],
  #[18, 29, 23]
]

/-- Position class for a 4×4 block position (0-15).
    Returns 0 for corner, 1 for other even-even, 2 for mixed. -/
def posClass (pos : Nat) : Nat :=
  let row := pos / 4
  let col := pos % 4
  if row % 2 == 0 && col % 2 == 0 then 0
  else if row % 2 == 0 || col % 2 == 0 then 2
  else 1

/-- Lookup MF value -/
def getMF (qpMod6 : Nat) (posClass : Nat) : Nat :=
  if h1 : qpMod6 < mfTable.size then
    let row := mfTable[qpMod6]
    if h2 : posClass < row.size then row[posClass] else 0
  else 0

/-- Lookup V value -/
def getV (qpMod6 : Nat) (posClass : Nat) : Nat :=
  if h1 : qpMod6 < vTable.size then
    let row := vTable[qpMod6]
    if h2 : posClass < row.size then row[posClass] else 0
  else 0

-- ============================================================================
-- Pure quantization functions
-- ============================================================================

/-- Forward quantization (intra mode).
    Input: signed coefficient, QP (0-51), position (0-15).
    Output: quantized level (signed). -/
def quantize (coeff : Int) (qp : Nat) (pos : Nat) : Int :=
  let qpMod6 := qp % 6
  let qpDiv6 := qp / 6
  let qbits := 15 + qpDiv6
  let f := (1 <<< qbits) / 3  -- intra rounding
  let mf := getMF qpMod6 (posClass pos)
  let absCoeff := coeff.natAbs
  let level := (absCoeff * mf + f) >>> qbits
  if coeff >= 0 then Int.ofNat level else -Int.ofNat level

/-- Inverse dequantization.
    Input: quantized level (signed), QP (0-51), position (0-15).
    Output: reconstructed coefficient (signed). -/
def dequantize (level : Int) (qp : Nat) (pos : Nat) : Int :=
  let qpMod6 := qp % 6
  let qpDiv6 := qp / 6
  let v := getV qpMod6 (posClass pos)
  level * Int.ofNat v * Int.ofNat (1 <<< qpDiv6)

/-- Quantize a full 4×4 block -/
def quantizeBlock (coeffs : Array Int) (qp : Nat) : Array Int :=
  (List.range 16).toArray.map fun i =>
    if h : i < coeffs.size then quantize coeffs[i] qp i else 0

/-- Dequantize a full 4×4 block -/
def dequantizeBlock (levels : Array Int) (qp : Nat) : Array Int :=
  (List.range 16).toArray.map fun i =>
    if h : i < levels.size then dequantize levels[i] qp i else 0

-- ============================================================================
-- QP parameter computation (for parameterized hardware modules)
-- ============================================================================

/-- Compute dequantization V*scale values for a given QP.
    Returns (vscale0, vscale1, vscale2) for position classes (corner, other-even, mixed). -/
def dequantScales (qp : Nat) : Nat × Nat × Nat :=
  let qpMod6 := qp % 6
  let qpDiv6 := qp / 6
  let scale := 1 <<< qpDiv6
  (getV qpMod6 0 * scale, getV qpMod6 1 * scale, getV qpMod6 2 * scale)

/-- Compute forward quantization parameters for a given QP.
    Returns (mf0, mf1, mf2, f, qbits) where mfN are MF per position class,
    f is the rounding offset, and qbits is the shift amount. -/
def quantParams (qp : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let qpMod6 := qp % 6
  let qpDiv6 := qp / 6
  let qbits := 15 + qpDiv6
  let f := (1 <<< qbits) / 3
  (getMF qpMod6 0, getMF qpMod6 1, getMF qpMod6 2, f, qbits)

-- ============================================================================
-- Golden value verification
-- ============================================================================

-- DCT coefficients from test block 1
private def testCoeffs : Array Int :=
  #[136, -28, 0, -4, -112, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0]

-- QP=0 golden values from C++
private def goldenQuantQP0 : Array Int :=
  #[54, -7, 0, -1, -27, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0]

#eval do
  let q := quantizeBlock testCoeffs 0
  IO.println s!"Quant QP=0: {q}"
  IO.println s!"Golden:     {goldenQuantQP0}"
  IO.println s!"Match: {q == goldenQuantQP0}"

  -- Verify zero preservation
  IO.println s!"quant(0, 20, 0) = {quantize 0 20 0}"

  -- Verify sign preservation
  IO.println s!"quant(136, 10, 0) = {quantize 136 10 0}"
  IO.println s!"quant(-136, 10, 0) = {quantize (-136) 10 0}"

end Sparkle.IP.Video.H264.Quant
