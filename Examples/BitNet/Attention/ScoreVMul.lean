/-
  Hespera Attention — Score-V Multiplication

  Computes attention-weighted V output for one head:
    out[j] = Σ_{i=0}^{seqLen-1} weight[i] × V[i][j]  >> 24

  - weight[i]: Q8.24 (32-bit) from softmax
  - V[i][j]: INT8 (8-bit), sign-extended to 32-bit before multiply
  - Product: 64-bit (safe: max |w|=2^24, max |v|=128, product < 2^31)
  - Sum: via buildAdderTree (reused from BitLinear/Core.lean)
  - Final: asr 24 → slice [31:0]

  No FSM — pure combinational datapath.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Generate the weighted sum for one output element j:
    out[j] = (Σ_i weight[i] × V[i][j]) >> 24

    Multiplies each Q8.24 weight by the sign-extended INT8 V value,
    then sums with an adder tree and shifts right by 24. -/
def generateWeightedVElement (seqLen j : Nat)
    (weightRefs : Array SizedExpr) (mulWidth : Nat) : CircuitM SizedExpr := do
  let mut products : Array SizedExpr := #[]
  for i in [:seqLen] do
    -- Sign-extend V[i][j] from 8 to mulWidth bits
    let vRef : SizedExpr := { expr := .ref s!"v_{i}_{j}", width := qkvBits }
    let vExt ← signExtendExpr vRef mulWidth

    -- Sign-extend weight[i] to mulWidth bits
    let wExt ← signExtendExpr weightRefs[i]! mulWidth

    -- Multiply
    let prodWire ← makeWire s!"sv_prod_{j}_{i}" (.bitVector mulWidth)
    emitAssign prodWire (Expr.mul wExt.expr vExt.expr)
    products := products.push { expr := .ref prodWire, width := mulWidth }

  -- Adder tree reduction
  let noPipelineCfg : GeneratorConfig := {
    baseBitWidth := mulWidth
    pipelineEvery := 0
  }
  let sum ← buildAdderTree products 0 noPipelineCfg

  -- Arithmetic shift right by 24 (Q8.24 back to integer)
  let shiftWire ← makeWire s!"sv_shift_{j}" (.bitVector sum.width)
  emitAssign shiftWire (Expr.op .asr [sum.expr, .const softmaxFracBits sum.width])

  -- Slice to 32-bit output
  let outWire ← makeWire s!"sv_out_{j}" (.bitVector softmaxTotalBits)
  emitAssign outWire (Expr.slice (.ref shiftWire) (softmaxTotalBits - 1) 0)

  return { expr := .ref outWire, width := softmaxTotalBits }

/-- Generate the complete Score-V multiply module.

    Inputs:  weight_0..weight_{seqLen-1}[31:0] (Q8.24 from softmax),
             v_0_0..v_{seqLen-1}_{headDim-1}[7:0] (INT8 V cache)
    Outputs: out_0..out_{headDim-1}[31:0] -/
def generateScoreVMul (seqLen headDim : Nat) : CircuitM Unit := do
  -- Weight inputs
  let mut weightRefs : Array SizedExpr := #[]
  for i in [:seqLen] do
    addInput s!"weight_{i}" (.bitVector softmaxTotalBits)
    weightRefs := weightRefs.push { expr := .ref s!"weight_{i}", width := softmaxTotalBits }

  -- V cache inputs: v_{position}_{element}
  for i in [:seqLen] do
    for j in [:headDim] do
      addInput s!"v_{i}_{j}" (.bitVector qkvBits)

  -- Multiply width: 40 bits is safe (2^24 × 128 < 2^31 < 2^39)
  let mulWidth := 40

  -- Generate weighted sum for each output element
  for j in [:headDim] do
    let result ← generateWeightedVElement seqLen j weightRefs mulWidth
    addOutput s!"out_{j}" (.bitVector softmaxTotalBits)
    emitAssign s!"out_{j}" result.expr

/-- Build a standalone Score-V multiply module -/
def buildScoreVMul (seqLen headDim : Nat) : Module :=
  CircuitM.runModule s!"ScoreVMul_{seqLen}x{headDim}" do
    generateScoreVMul seqLen headDim

end Sparkle.Examples.BitNet.Attention
