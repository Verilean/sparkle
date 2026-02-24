/-
  BitNet BitLinear Core — Pipelined Dataflow Architecture

  Ternary weights are hardwired into combinational logic at Lean elaboration time.
  - Weight=0 connections are pruned entirely (no adders, no wires)
  - Weight=±1 uses pass-through or negate (no multipliers)
  - Additions form a binary adder tree with automatic pipeline register insertion
  - Bit-width propagation: A[n] + B[m] → result is max(n,m)+1 bits
-/

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

/-- Generate the MAC stage: for each weight, emit the appropriate signal. -/
def generateMACStage (weights : Array Int) (cfg : GeneratorConfig)
    : CircuitM (Array SizedExpr) := do
  let mut results : Array SizedExpr := #[]
  for i in [:weights.size] do
    let w := weights[i]!
    if w == 1 then
      let se : SizedExpr := { expr := .ref s!"act_{i}", width := cfg.baseBitWidth }
      results := results.push se
    else if w == -1 then
      let negWire ← makeWire s!"neg_{i}" (.bitVector cfg.baseBitWidth)
      emitAssign negWire (Expr.sub (.const 0 cfg.baseBitWidth) (.ref s!"act_{i}"))
      let se : SizedExpr := { expr := .ref negWire, width := cfg.baseBitWidth }
      results := results.push se
  return results

/-- Insert pipeline registers for all elements in the array. -/
def insertPipelineRegs (inputs : Array SizedExpr) (level : Nat)
    (cfg : GeneratorConfig) : CircuitM (Array SizedExpr) := do
  let mut pipeResults : Array SizedExpr := #[]
  for i in [:inputs.size] do
    let r : SizedExpr := inputs[i]!
    let regOut ← emitRegister s!"pipe_L{level}_{i}" cfg.clockName cfg.resetName
      r.expr 0 (.bitVector r.width)
    let se : SizedExpr := { expr := .ref regOut, width := r.width }
    pipeResults := pipeResults.push se
  return pipeResults

/-- Build a binary adder tree with automatic bit-width propagation and
    configurable pipeline register insertion. -/
partial def buildAdderTree (inputs : Array SizedExpr) (level : Nat)
    (cfg : GeneratorConfig) : CircuitM SizedExpr := do
  if inputs.size == 0 then
    return { expr := .const 0 cfg.baseBitWidth, width := cfg.baseBitWidth }
  if inputs.size == 1 then
    return inputs[0]!

  let mut results : Array SizedExpr := #[]
  let pairs := inputs.size / 2

  for i in [:pairs] do
    let a : SizedExpr := inputs[2 * i]!
    let b : SizedExpr := inputs[2 * i + 1]!
    let outWidth := addBitWidth a.width b.width
    let aExt ← signExtendExpr a outWidth
    let bExt ← signExtendExpr b outWidth
    let sumWire ← makeWire s!"sum_L{level}_{i}" (.bitVector outWidth)
    emitAssign sumWire (Expr.add aExt.expr bExt.expr)
    let se : SizedExpr := { expr := .ref sumWire, width := outWidth }
    results := results.push se

  if inputs.size % 2 == 1 then
    let carry : SizedExpr := inputs[inputs.size - 1]!
    if results.size > 0 then
      let sumWidth := (results[0]!  : SizedExpr).width
      let carryExt ← signExtendExpr carry sumWidth
      results := results.push carryExt
    else
      results := results.push carry

  if cfg.pipelineEvery > 0 && level % cfg.pipelineEvery == cfg.pipelineEvery - 1 then
    results ← insertPipelineRegs results level cfg

  buildAdderTree results (level + 1) cfg

/-- Top-level pipelined BitLinear generator. -/
def generateBitLinearPipelined (weights : Array Int) (cfg : GeneratorConfig)
    : CircuitM Unit := do
  addInput cfg.clockName .bit
  addInput cfg.resetName .bit

  for i in [:weights.size] do
    if weights[i]! != 0 then
      addInput s!"act_{i}" (.bitVector cfg.baseBitWidth)

  let macs ← generateMACStage weights cfg

  if macs.size == 0 then
    addOutput "result" (.bitVector cfg.baseBitWidth)
    emitAssign "result" (.const 0 cfg.baseBitWidth)
    return

  let finalSum ← buildAdderTree macs 0 cfg

  addOutput "result" (.bitVector finalSum.width)
  emitAssign "result" finalSum.expr

end Sparkle.Examples.BitNet.BitLinear
