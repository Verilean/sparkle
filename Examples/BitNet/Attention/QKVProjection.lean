/-
  Hespera Attention — QKV Projection

  Reuses the exact BitLinear (ternary-weight, multiplier-less) generator
  to compute Q, K, V projections for one attention head.

  For each output element j in [0, headDim):
    q[j] = BitLinear(x, q_weights[j]) → Scale → QuantizeToINT8
    k[j] = BitLinear(x, k_weights[j]) → Scale → QuantizeToINT8
    v[j] = BitLinear(x, v_weights[j]) → Scale → QuantizeToINT8

  Fully pipelined — no FSM. All headDim output rows computed in parallel.
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Attention.Quantize

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Generate a single BitLinear row (one output element) using shared activation
    inputs. Reuses the MAC stage + adder tree pattern from BitLinear.Core.

    Weights are hardwired at elaboration time:
    - w[i] = 0  → pruned (no hardware)
    - w[i] = +1 → pass-through
    - w[i] = -1 → negate (0 - x_i)

    The input activations are referenced as `x_0`, `x_1`, etc.

    Returns the accumulator result as a SizedExpr. -/
def generateBitLinearRow (namePrefix : String) (weights : Array Int)
    (cfg : GeneratorConfig) : CircuitM SizedExpr := do
  -- MAC stage: prune zeros, negate where needed (same as Core.generateMACStage
  -- but with prefixed wire names and shared "x_i" inputs)
  let mut macs : Array SizedExpr := #[]
  for i in [:weights.size] do
    let w := weights[i]!
    if w == 1 then
      macs := macs.push { expr := .ref s!"x_{i}", width := cfg.baseBitWidth }
    else if w == -1 then
      let negWire ← makeWire s!"{namePrefix}_neg_{i}" (.bitVector cfg.baseBitWidth)
      emitAssign negWire (Expr.sub (.const 0 cfg.baseBitWidth) (.ref s!"x_{i}"))
      macs := macs.push { expr := .ref negWire, width := cfg.baseBitWidth }
    -- w == 0: pruned

  if macs.size == 0 then
    return { expr := .const 0 cfg.baseBitWidth, width := cfg.baseBitWidth }

  -- Adder tree reduction (reuses BitLinear infrastructure)
  buildAdderTree macs 0 cfg

/-- Generate scale multiplication with a hardwired constant scale factor.

    RTL: sign-extend acc to mulProductBits → multiply by constant → asr 24 → [31:0] -/
def generateScaleConst (accResult : SizedExpr) (scaleVal : Int)
    : CircuitM SizedExpr := do
  let accExt ← signExtendExpr accResult mulProductBits
  let prodWire ← makeWire "scl_prod" (.bitVector mulProductBits)
  emitAssign prodWire (Expr.mul accExt.expr (.const scaleVal mulProductBits))
  let shiftWire ← makeWire "scl_shifted" (.bitVector mulProductBits)
  emitAssign shiftWire (Expr.op .asr [.ref prodWire, .const scaleFracBits mulProductBits])
  let resultWire ← makeWire "scl_result" (.bitVector actTotalBits)
  emitAssign resultWire (Expr.slice (.ref shiftWire) (actTotalBits - 1) 0)
  return { expr := .ref resultWire, width := actTotalBits }

/-- Generate the complete QKV projection for one attention head.

    For each of Q, K, V and each output row j:
      acc = BitLinearRow(x, weights[j])
      scaled = acc × scale[j] (Q8.24)
      quantized = INT8_Quantize(scaled, quantShift)

    Inputs:  clk, rst, x_0..x_{inDim-1}[baseBitWidth-1:0]
    Outputs: q_0..q_{headDim-1}[7:0],
             k_0..k_{headDim-1}[7:0],
             v_0..v_{headDim-1}[7:0]

    Weight arrays: [headDim][inDim] ternary values
    Scale arrays:  [headDim] Q8.24 scale factors -/
def generateQKVProjection
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (quantShift : Nat)
    (cfg : GeneratorConfig) : CircuitM Unit := do
  let headDim := qWeights.size
  let inDim := if headDim > 0 then qWeights[0]!.size else 0

  -- Shared activation inputs
  addInput cfg.clockName .bit
  addInput cfg.resetName .bit
  for i in [:inDim] do
    addInput s!"x_{i}" (.bitVector cfg.baseBitWidth)

  -- Generate Q projections
  for j in [:headDim] do
    let acc ← generateBitLinearRow s!"q_row{j}" qWeights[j]! cfg
    let qScale := if h : j < qScales.size then qScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc qScale
    let quantized ← generateQuantizeInt8 scaled quantShift
    addOutput s!"q_{j}" (.bitVector qkvBits)
    emitAssign s!"q_{j}" quantized.expr

  -- Generate K projections
  for j in [:headDim] do
    let acc ← generateBitLinearRow s!"k_row{j}" kWeights[j]! cfg
    let kScale := if h : j < kScales.size then kScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc kScale
    let quantized ← generateQuantizeInt8 scaled quantShift
    addOutput s!"k_{j}" (.bitVector qkvBits)
    emitAssign s!"k_{j}" quantized.expr

  -- Generate V projections
  for j in [:headDim] do
    let acc ← generateBitLinearRow s!"v_row{j}" vWeights[j]! cfg
    let vScale := if h : j < vScales.size then vScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc vScale
    let quantized ← generateQuantizeInt8 scaled quantShift
    addOutput s!"v_{j}" (.bitVector qkvBits)
    emitAssign s!"v_{j}" quantized.expr

/-- Build a standalone QKV Projection module -/
def buildQKVProjection
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (quantShift : Nat)
    (cfg : GeneratorConfig) : Module :=
  let headDim := qWeights.size
  CircuitM.runModule s!"QKV_Projection_{headDim}head" do
    generateQKVProjection qWeights kWeights vWeights
      qScales kScales vScales quantShift cfg

end Sparkle.Examples.BitNet.Attention
