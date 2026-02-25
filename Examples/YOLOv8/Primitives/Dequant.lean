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
    Uses the signal-compatible pattern: `.map (BitVec.signExtend 8 ·)` -/
def dequantInt4ToInt8 (w4 : Signal dom (BitVec 4)) : Signal dom (BitVec 8) :=
  w4.map (BitVec.signExtend 8 ·)

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

/-- Sign-extend an 8-bit signal to 32-bit for accumulation -/
def extendInt8ToInt32 (a : Signal dom (BitVec 8)) : Signal dom (BitVec 32) :=
  a.map (BitVec.signExtend 32 ·)

/-- Top-level synthesizable dequantization: packed INT4 byte → two INT8 outputs -/
def dequantPacked {dom : DomainConfig}
    (packed : Signal dom (BitVec 8))
    : Signal dom (BitVec 8 × BitVec 8) :=
  let lower := dequantLowerToInt8 packed
  let upper := dequantUpperToInt8 packed
  bundle2 lower upper

-- Note: `.map (BitVec.signExtend ·)` pattern not yet supported by synthesizer.
-- #synthesizeVerilog dequantPacked

end Sparkle.Examples.YOLOv8.Primitives.Dequant
