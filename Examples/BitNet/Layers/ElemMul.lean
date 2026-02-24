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

def generateElemMul (aName bName outputName : String) : CircuitM Unit := do
  let aRef : SizedExpr := { expr := .ref aName, width := actTotalBits }
  let bRef : SizedExpr := { expr := .ref bName, width := actTotalBits }
  let aExt ← signExtendExpr aRef squaredBits
  let bExt ← signExtendExpr bRef squaredBits
  let prodWire ← makeWire "emul_prod" (.bitVector squaredBits)
  emitAssign prodWire (Expr.mul aExt.expr bExt.expr)
  let shiftWire ← makeWire "emul_shifted" (.bitVector squaredBits)
  emitAssign shiftWire (Expr.op .asr [.ref prodWire, .const 16 squaredBits])
  let resultWire ← makeWire "emul_result" (.bitVector actTotalBits)
  emitAssign resultWire (Expr.slice (.ref shiftWire) (actTotalBits - 1) 0)
  emitAssign outputName (.ref resultWire)

def buildElemMul : Module :=
  CircuitM.runModule "ElemMul" do
    addInput "a" (.bitVector actTotalBits)
    addInput "b" (.bitVector actTotalBits)
    addOutput "y" (.bitVector actTotalBits)
    generateElemMul "a" "b" "y"
end Sparkle.Examples.BitNet.Layers
