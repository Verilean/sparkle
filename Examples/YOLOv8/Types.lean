/-
  YOLOv8n-WorldV2 Types

  BitVec type aliases and arithmetic helpers for INT4/INT8 quantized inference.
-/

import Examples.YOLOv8.Config

namespace Sparkle.Examples.YOLOv8

-- ============================================================================
-- Core Type Aliases
-- ============================================================================

/-- Signed 4-bit weight (INT4) -/
abbrev WeightInt4 := BitVec weightBits

/-- Signed 8-bit activation (INT8) -/
abbrev ActivationInt8 := BitVec activationBits

/-- 32-bit signed accumulator for MAC operations -/
abbrev Accumulator := BitVec accumulatorBits

/-- 16-bit requantization scale factor -/
abbrev ScaleVal := BitVec scaleBits

/-- 5-bit shift amount for requantization -/
abbrev ShiftVal := BitVec shiftBits

/-- Packed byte containing two INT4 weights -/
abbrev PackedWeightByte := BitVec 8

-- ============================================================================
-- Arithmetic Helpers (Pure Lean for simulation/testing)
-- ============================================================================

/-- Sign-extend INT4 to INT8 -/
def signExtendInt4ToInt8 (w : WeightInt4) : ActivationInt8 :=
  w.signExtend 8

/-- Sign-extend INT8 to INT32 for accumulation -/
def signExtendInt8ToInt32 (a : ActivationInt8) : Accumulator :=
  a.signExtend 32

/-- MAC operation: acc += w_int4 * a_int8 (in INT32) -/
def macOp (acc : BitVec 32) (w : BitVec 4) (a : BitVec 8) : BitVec 32 :=
  let wExt : BitVec 32 := (w.signExtend 8).signExtend 32
  let aExt : BitVec 32 := a.signExtend 32
  let product : BitVec 32 := wExt * aExt
  acc + product

/-- Requantize: output = clamp((acc * scale) >> shift, -128, 127)
    Performs multiply-shift to avoid runtime division. -/
def requantizeOp (acc : BitVec 32) (scale : BitVec 16) (shift : BitVec 5) : BitVec 8 :=
  let accInt := acc.toInt
  let scaleInt := (scale.signExtend 32 : BitVec 32).toInt
  let product := accInt * scaleInt
  let shifted := product / (2 ^ shift.toNat : Int)
  -- Clamp to [-128, 127]
  let clamped :=
    if shifted > 127 then 127
    else if shifted < -128 then -128
    else shifted
  BitVec.ofInt 8 clamped

/-- ReLU on INT8: max(0, x) -/
def reluInt8 (x : BitVec 8) : BitVec 8 :=
  if x.toInt < 0 then 0#8 else x

/-- Extract lower INT4 from a packed byte (bits [3:0]) -/
def extractLowerInt4 (packed : BitVec 8) : BitVec 4 :=
  packed.extractLsb' 0 4

/-- Extract upper INT4 from a packed byte (bits [7:4]) -/
def extractUpperInt4 (packed : BitVec 8) : BitVec 4 :=
  packed.extractLsb' 4 4

/-- Signed saturating addition of two INT8 values -/
def saturatingAddInt8 (a b : BitVec 8) : BitVec 8 :=
  let sum := a.toInt + b.toInt
  if sum > 127 then 127#8
  else if sum < -128 then BitVec.ofInt 8 (-128)
  else BitVec.ofInt 8 sum

/-- Signed max of two INT8 values -/
def maxInt8 (a b : BitVec 8) : BitVec 8 :=
  if a.toInt >= b.toInt then a else b

end Sparkle.Examples.YOLOv8
