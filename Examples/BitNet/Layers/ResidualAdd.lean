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

def generateResidualAdd (aName bName outputName : String) : CircuitM Unit := do
  let extWidth := actTotalBits + 1
  let aRef : SizedExpr := { expr := .ref aName, width := actTotalBits }
  let bRef : SizedExpr := { expr := .ref bName, width := actTotalBits }
  let aExt ← signExtendExpr aRef extWidth
  let bExt ← signExtendExpr bRef extWidth
  let sumWire ← makeWire "resadd_sum" (.bitVector extWidth)
  emitAssign sumWire (Expr.add aExt.expr bExt.expr)
  let topBits ← makeWire "resadd_top2" (.bitVector 2)
  emitAssign topBits (Expr.slice (.ref sumWire) (extWidth - 1) (extWidth - 2))
  let lowBits ← makeWire "resadd_low" (.bitVector actTotalBits)
  emitAssign lowBits (Expr.slice (.ref sumWire) (actTotalBits - 1) 0)
  let maxPos : Int := (2^31 : Nat) - 1
  let maxNeg : Int := -(2^31 : Nat)
  let posOvf ← makeWire "resadd_pos_ovf" (.bitVector 1)
  emitAssign posOvf (Expr.op .eq [.ref topBits, .const 0b01 2])
  let negOvf ← makeWire "resadd_neg_ovf" (.bitVector 1)
  emitAssign negOvf (Expr.op .eq [.ref topBits, .const 0b10 2])
  let satResult ← makeWire "resadd_sat" (.bitVector actTotalBits)
  emitAssign satResult (Expr.mux (.ref negOvf)
    (.const maxNeg actTotalBits)
    (Expr.mux (.ref posOvf)
      (.const maxPos actTotalBits)
      (.ref lowBits)))
  emitAssign outputName (.ref satResult)

def buildResidualAdd : Module :=
  CircuitM.runModule "ResidualAdd" do
    addInput "a" (.bitVector actTotalBits)
    addInput "b" (.bitVector actTotalBits)
    addOutput "y" (.bitVector actTotalBits)
    generateResidualAdd "a" "b" "y"
end Sparkle.Examples.BitNet.Layers
