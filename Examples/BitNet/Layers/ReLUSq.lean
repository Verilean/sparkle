import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth

namespace Sparkle.Examples.BitNet.Layers
open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

def generateReLUSq (inputName outputName : String) : CircuitM Unit := do
  let inputRef : SizedExpr := { expr := .ref inputName, width := actTotalBits }
  let signBit := Expr.slice inputRef.expr (actTotalBits - 1) (actTotalBits - 1)
  let inputExt ← signExtendExpr inputRef squaredBits
  let sqWire ← makeWire "relusq_squared" (.bitVector squaredBits)
  emitAssign sqWire (Expr.mul inputExt.expr inputExt.expr)
  let shiftWire ← makeWire "relusq_shifted" (.bitVector squaredBits)
  emitAssign shiftWire (Expr.op .asr [.ref sqWire, .const 16 squaredBits])
  let posResult ← makeWire "relusq_pos" (.bitVector actTotalBits)
  emitAssign posResult (Expr.slice (.ref shiftWire) (actTotalBits - 1) 0)
  emitAssign outputName (Expr.mux signBit (.const 0 actTotalBits) (.ref posResult))

def buildReLUSq : Module :=
  CircuitM.runModule "ReLUSq" do
    addInput "x" (.bitVector actTotalBits)
    addOutput "y" (.bitVector actTotalBits)
    generateReLUSq "x" "y"
end Sparkle.Examples.BitNet.Layers
