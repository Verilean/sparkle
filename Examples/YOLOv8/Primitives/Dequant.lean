/-
  INT4 Dequantization — Signal DSL

  Sign-extends 4-bit weights to 8-bit for MAC operations.
  Also provides INT4 extraction from packed bytes.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Types

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Sparkle.Examples.YOLOv8.Primitives.Dequant

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8

variable {dom : DomainConfig}

/-- Sign-extend a 4-bit signal to 8-bit signal.
    Synthesizable: extracts MSB, muxes between 1-padded and 0-padded concat. -/
def dequantInt4ToInt8 (w4 : Signal dom (BitVec 4)) : Signal dom (BitVec 8) :=
  let msb := w4.map (BitVec.extractLsb' 3 1 ·)
  let isNeg := (· == ·) <$> msb <*> Signal.pure 1#1
  let padOnes := (· ++ ·) <$> Signal.pure 15#4 <*> w4   -- 1111 ++ w4
  let padZeros := (· ++ ·) <$> Signal.pure 0#4 <*> w4   -- 0000 ++ w4
  Signal.mux isNeg padOnes padZeros

/-- Extract lower INT4 (bits [3:0]) from a packed 8-bit signal -/
def extractLowerInt4Signal (packed : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  packed.map (BitVec.extractLsb' 0 4 ·)

/-- Extract upper INT4 (bits [7:4]) from a packed 8-bit signal -/
def extractUpperInt4Signal (packed : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  packed.map (BitVec.extractLsb' 4 4 ·)

/-- Full dequantize pipeline: extract lower INT4 from packed byte, sign-extend to INT8 -/
def dequantLowerToInt8 (packed : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  dequantInt4ToInt8 (extractLowerInt4Signal packed)

/-- Full dequantize pipeline: extract upper INT4 from packed byte, sign-extend to INT8 -/
def dequantUpperToInt8 (packed : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  dequantInt4ToInt8 (extractUpperInt4Signal packed)

/-- Sign-extend an 8-bit signal to 32-bit for accumulation.
    Synthesizable: MSB check + mux between 1-padded and 0-padded. -/
def extendInt8ToInt32 (a : Signal dom (BitVec 8)) : Signal dom (BitVec 32) :=
  let msb := a.map (BitVec.extractLsb' 7 1 ·)
  let isNeg := (· == ·) <$> msb <*> Signal.pure 1#1
  let padOnes := (· ++ ·) <$> Signal.pure (BitVec.ofNat 24 0xFFFFFF) <*> a
  let padZeros := (· ++ ·) <$> Signal.pure 0#24 <*> a
  Signal.mux isNeg padOnes padZeros

/-- Top-level synthesizable dequantization: packed INT4 byte → two INT8 outputs -/
def dequantPacked {dom : DomainConfig}
    (packed : Signal dom (BitVec 8))
    : Signal dom (BitVec 8 × BitVec 8) :=
  let lower := dequantLowerToInt8 packed
  let upper := dequantUpperToInt8 packed
  bundle2 lower upper

#synthesizeVerilog dequantPacked

end Sparkle.Examples.YOLOv8.Primitives.Dequant
