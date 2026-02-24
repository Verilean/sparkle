import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth

namespace Sparkle.Examples.BitNet.BitLinear

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

def generateScaleMultiply (accResult : SizedExpr) (scaleName : String)
    (_cfg : GeneratorConfig) : CircuitM SizedExpr := do
  let accExt ← signExtendExpr accResult mulProductBits
  let scaleRef : SizedExpr := { expr := .ref scaleName, width := scaleTotalBits }
  let scaleExt ← signExtendExpr scaleRef mulProductBits
  let prodWire ← makeWire "scale_prod" (.bitVector mulProductBits)
  emitAssign prodWire (Expr.mul accExt.expr scaleExt.expr)
  let shiftWire ← makeWire "scale_shifted" (.bitVector mulProductBits)
  emitAssign shiftWire (Expr.op .asr [.ref prodWire, .const scaleFracBits mulProductBits])
  let resultWire ← makeWire "scale_result" (.bitVector actTotalBits)
  emitAssign resultWire (Expr.slice (.ref shiftWire) (actTotalBits - 1) 0)
  return { expr := .ref resultWire, width := actTotalBits }

def buildScaleMultiply (cfg : GeneratorConfig) : Module :=
  CircuitM.runModule "ScaleMultiply" do
    addInput cfg.clockName .bit
    addInput cfg.resetName .bit
    addInput "acc" (.bitVector accBits)
    addInput "scale" (.bitVector scaleTotalBits)
    let accRef : SizedExpr := { expr := .ref "acc", width := accBits }
    let result ← generateScaleMultiply accRef "scale" cfg
    addOutput "result" (.bitVector actTotalBits)
    emitAssign "result" result.expr

end Sparkle.Examples.BitNet.BitLinear
