/-
  Hespera Attention — INT8 Quantization

  Combinational Q16.16 → INT8 quantizer with saturation.
  Arithmetic shift right by `quantShift`, then clamp to [-128, 127].

  No FSM — purely combinational, fits in the pipelined datapath.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Generate combinational INT8 quantization from a Q16.16 activation.

    1. Arithmetic shift right by `quantShift`
    2. Check if shifted value fits in INT8 (bits [31:7] all equal)
    3. Saturate to [-128, 127] if overflow

    Returns an 8-bit SizedExpr. -/
def generateQuantizeInt8 (inputExpr : SizedExpr) (quantShift : Nat)
    : CircuitM SizedExpr := do
  -- Arithmetic shift right
  let shiftWire ← makeWire "quant_shifted" (.bitVector actTotalBits)
  emitAssign shiftWire (Expr.op .asr [inputExpr.expr, .const quantShift actTotalBits])

  -- Bit 7 of the shifted value is the INT8 sign bit
  let int8Sign := Expr.slice (.ref shiftWire) 7 7

  -- Upper 24 bits (31:8) should all match bit 7 for no overflow
  let numUpper := actTotalBits - qkvBits  -- 24
  let actualUpper ← makeWire "quant_upper" (.bitVector numUpper)
  emitAssign actualUpper (Expr.slice (.ref shiftWire) (actTotalBits - 1) qkvBits)

  -- Expected upper bits: all copies of bit 7
  let expectedUpper ← makeWire "quant_expected" (.bitVector numUpper)
  emitAssign expectedUpper (Expr.mux int8Sign
    (.const ((1 <<< numUpper) - 1) numUpper)   -- all 1s (negative)
    (.const 0 numUpper))                        -- all 0s (positive)

  -- No overflow if upper bits match expected sign extension
  let noOverflow ← makeWire "quant_no_ovf" (.bitVector 1)
  emitAssign noOverflow (Expr.op .eq [.ref actualUpper, .ref expectedUpper])

  -- Overall sign bit (for saturation direction)
  let overallSign := Expr.slice (.ref shiftWire) (actTotalBits - 1) (actTotalBits - 1)

  -- Lower 8 bits (direct result when no overflow)
  let lower8 ← makeWire "quant_low8" (.bitVector qkvBits)
  emitAssign lower8 (Expr.slice (.ref shiftWire) (qkvBits - 1) 0)

  -- Saturated result:
  --   no overflow → lower 8 bits
  --   positive overflow → 0x7F (127)
  --   negative overflow → 0x80 (−128 in two's complement)
  let saturated ← makeWire "quant_sat" (.bitVector qkvBits)
  emitAssign saturated (Expr.mux (.ref noOverflow)
    (.ref lower8)
    (Expr.mux overallSign
      (.const 0x80 qkvBits)    -- negative overflow → −128
      (.const 0x7F qkvBits)))  -- positive overflow → 127

  return { expr := .ref saturated, width := qkvBits }

/-- Build a standalone Quantize module for testing.

    Input:  x[31:0] (Q16.16)
    Output: q[7:0]  (INT8) -/
def buildQuantize (quantShift : Nat) : Module :=
  CircuitM.runModule s!"QuantizeInt8_shift{quantShift}" do
    addInput "x" (.bitVector actTotalBits)
    addOutput "q" (.bitVector qkvBits)
    let xRef : SizedExpr := { expr := .ref "x", width := actTotalBits }
    let result ← generateQuantizeInt8 xRef quantShift
    emitAssign "q" result.expr

end Sparkle.Examples.BitNet.Attention
