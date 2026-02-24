import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core

namespace Sparkle.Examples.BitNet.BitLinear

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

def generateDynamicMAC (inDim : Nat) (cfg : GeneratorConfig)
    : CircuitM (Array SizedExpr) := do
  let mut results : Array SizedExpr := #[]
  for i in [:inDim] do
    let negWire ← makeWire s!"neg_{i}" (.bitVector cfg.baseBitWidth)
    emitAssign negWire (Expr.sub (.const 0 cfg.baseBitWidth) (.ref s!"act_{i}"))
    let decodedWire ← makeWire s!"decoded_{i}" (.bitVector cfg.baseBitWidth)
    emitAssign decodedWire
      (Expr.mux
        (Expr.op .eq [.ref s!"w_{i}", .const 0b10 2])
        (.ref s!"act_{i}")
        (Expr.mux
          (Expr.op .eq [.ref s!"w_{i}", .const 0b00 2])
          (.ref negWire)
          (.const 0 cfg.baseBitWidth)))
    results := results.push { expr := .ref decodedWire, width := cfg.baseBitWidth }
  return results

def generateDynamicBitLinearRow (namePrefix : String) (inDim : Nat)
    (cfg : GeneratorConfig) : CircuitM SizedExpr := do
  for i in [:inDim] do
    addInput s!"{namePrefix}w_{i}" (.bitVector 2)
    addInput s!"{namePrefix}act_{i}" (.bitVector cfg.baseBitWidth)
  let macs ← generateDynamicMAC inDim cfg
  if macs.size == 0 then
    return { expr := .const 0 cfg.baseBitWidth, width := cfg.baseBitWidth }
  buildAdderTree macs 0 cfg

def buildDynamicBitLinear (inDim : Nat) (cfg : GeneratorConfig) : Module :=
  CircuitM.runModule s!"DynamicBitLinear_{inDim}" do
    addInput cfg.clockName .bit
    addInput cfg.resetName .bit
    for i in [:inDim] do
      addInput s!"w_{i}" (.bitVector 2)
      addInput s!"act_{i}" (.bitVector cfg.baseBitWidth)
    let macs ← generateDynamicMAC inDim cfg
    if macs.size == 0 then
      addOutput "result" (.bitVector cfg.baseBitWidth)
      emitAssign "result" (.const 0 cfg.baseBitWidth)
      return
    let finalSum ← buildAdderTree macs 0 cfg
    addOutput "result" (.bitVector finalSum.width)
    emitAssign "result" finalSum.expr

end Sparkle.Examples.BitNet.BitLinear
