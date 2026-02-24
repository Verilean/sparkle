/-
  Sparkle Examples — BitNet Attention — Multi-Head Attention

  Structural composition of multiple attention heads:
  1. Instantiate nHeads full attention heads (each with different weights)
  2. Concatenate outputs: head{h}_out_{j} → concat_{h*headDim + j}
  3. Output projection: BitLinear row for each output element

  All inlined (no emitInstance), fully combinational for demo sizes.

  Demo: nHeads=2, headDim=2, inDim=4, seqLen=4
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.Attention.Quantize
import Examples.BitNet.Attention.DotProduct
import Examples.BitNet.Attention.QKVProjection
import Examples.BitNet.Attention.Softmax
import Examples.BitNet.Attention.ScoreVMul
import Examples.BitNet.Attention.Top

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Configuration for multi-head attention -/
structure MultiHeadConfig where
  nHeads  : Nat  -- Number of attention heads
  headDim : Nat  -- Dimension per head
  inDim   : Nat  -- Input dimension
  seqLen  : Nat  -- Number of cached KV positions
  quantShift : Nat := 10
  dkShift    : Nat := 1
  deriving Repr, BEq

/-- Total concatenated dimension = nHeads × headDim -/
def MultiHeadConfig.concatDim (c : MultiHeadConfig) : Nat := c.nHeads * c.headDim

/-- Generate multi-head attention with output projection.

    For each head h in [0, nHeads):
      - QKV projection from shared x inputs
      - Dot product Q·K^T for each cached position
      - Softmax over scores
      - Score-V multiply → headDim outputs

    Then concatenate all head outputs and apply output projection
    (BitLinear rows) to produce the final modelDim output.

    Inputs:
      clk, rst,
      x_0..x_{inDim-1}[baseBitWidth-1:0],
      k_cache_h{h}_{pos}_{j}[7:0],
      v_cache_h{h}_{pos}_{j}[7:0]

    Outputs:
      mha_out_0..mha_out_{modelDim-1}[31:0] -/
def generateMultiHeadAttention
    (config : MultiHeadConfig)
    (allQWeights allKWeights allVWeights : Array (Array (Array Int)))
    (allQScales allKScales allVScales : Array (Array Int))
    (outProjWeights : Array (Array Int))
    (outProjScales : Array Int)
    (cfg : GeneratorConfig) : CircuitM Unit := do
  -- ==========================================
  -- Shared inputs
  -- ==========================================
  addInput cfg.clockName .bit
  addInput cfg.resetName .bit
  for i in [:config.inDim] do
    addInput s!"x_{i}" (.bitVector cfg.baseBitWidth)

  -- KV cache inputs per head
  for h in [:config.nHeads] do
    for pos in [:config.seqLen] do
      for j in [:config.headDim] do
        addInput s!"k_cache_h{h}_{pos}_{j}" (.bitVector qkvBits)
    for pos in [:config.seqLen] do
      for j in [:config.headDim] do
        addInput s!"v_cache_h{h}_{pos}_{j}" (.bitVector qkvBits)

  let noPipelineCfg : GeneratorConfig := {
    baseBitWidth := softmaxTotalBits
    pipelineEvery := 0
  }

  -- ==========================================
  -- Per-head computation
  -- ==========================================
  let mut concatOutputs : Array SizedExpr := #[]

  for h in [:config.nHeads] do
    let qWeights := allQWeights[h]!
    let kWeights := allKWeights[h]!
    let vWeights := allVWeights[h]!
    let qScales := allQScales[h]!
    let kScales := allKScales[h]!
    let vScales := allVScales[h]!

    -- QKV Projection for this head (query from current x)
    let mut qOutputs : Array SizedExpr := #[]
    for j in [:config.headDim] do
      let acc ← generateBitLinearRow s!"h{h}_q_row{j}" qWeights[j]! cfg
      let qScale := if hj : j < qScales.size then qScales[j] else (2^scaleFracBits : Nat)
      let scaled ← generateScaleConst acc qScale
      let quantized ← generateQuantizeInt8 scaled config.quantShift
      let qWire ← makeWire s!"h{h}_q_{j}" (.bitVector qkvBits)
      emitAssign qWire quantized.expr
      qOutputs := qOutputs.push { expr := .ref qWire, width := qkvBits }

    -- K and V projections for current token (not used if cache pre-filled)
    for j in [:config.headDim] do
      let acc ← generateBitLinearRow s!"h{h}_k_row{j}" kWeights[j]! cfg
      let kScale := if hj : j < kScales.size then kScales[j] else (2^scaleFracBits : Nat)
      let scaled ← generateScaleConst acc kScale
      let quantized ← generateQuantizeInt8 scaled config.quantShift
      let kWire ← makeWire s!"h{h}_k_cur_{j}" (.bitVector qkvBits)
      emitAssign kWire quantized.expr

    for j in [:config.headDim] do
      let acc ← generateBitLinearRow s!"h{h}_v_row{j}" vWeights[j]! cfg
      let vScale := if hj : j < vScales.size then vScales[j] else (2^scaleFracBits : Nat)
      let scaled ← generateScaleConst acc vScale
      let quantized ← generateQuantizeInt8 scaled config.quantShift
      let vWire ← makeWire s!"h{h}_v_cur_{j}" (.bitVector qkvBits)
      emitAssign vWire quantized.expr

    -- Dot product Q·K^T for each cached position
    let mut scores : Array SizedExpr := #[]
    for pos in [:config.seqLen] do
      let mut products : Array SizedExpr := #[]
      for j in [:config.headDim] do
        let qExt ← signExtendExpr qOutputs[j]! productBits
        let kRef : SizedExpr := { expr := .ref s!"k_cache_h{h}_{pos}_{j}", width := qkvBits }
        let kExt ← signExtendExpr kRef productBits
        let prodWire ← makeWire s!"h{h}_qk_{pos}_{j}" (.bitVector productBits)
        emitAssign prodWire (Expr.mul qExt.expr kExt.expr)
        products := products.push { expr := .ref prodWire, width := productBits }

      if products.size == 0 then
        let zeroWire ← makeWire s!"h{h}_score_{pos}" (.bitVector productBits)
        emitAssign zeroWire (.const 0 productBits)
        scores := scores.push { expr := .ref zeroWire, width := productBits }
      else
        let dotSum ← buildAdderTree products 0 cfg
        if config.dkShift > 0 then
          let scoreWire ← makeWire s!"h{h}_score_{pos}" (.bitVector dotSum.width)
          emitAssign scoreWire (Expr.op .asr [dotSum.expr, .const config.dkShift dotSum.width])
          scores := scores.push { expr := .ref scoreWire, width := dotSum.width }
        else
          let scoreWire ← makeWire s!"h{h}_score_{pos}" (.bitVector dotSum.width)
          emitAssign scoreWire dotSum.expr
          scores := scores.push { expr := .ref scoreWire, width := dotSum.width }

    let scoreBits := if scores.size > 0 then scores[0]!.width else productBits

    -- Softmax
    let maxVal ← buildMaxTree scores 0
    let expLUT := generateExpLUT
    let mut expVals : Array SizedExpr := #[]
    for pos in [:config.seqLen] do
      let diffWire ← makeWire s!"h{h}_diff_{pos}" (.bitVector scoreBits)
      emitAssign diffWire (Expr.sub scores[pos]!.expr maxVal.expr)
      let absDiffWire ← makeWire s!"h{h}_abs_{pos}" (.bitVector scoreBits)
      emitAssign absDiffWire (Expr.sub (.const 0 scoreBits) (.ref diffWire))

      let idxWire ← makeWire s!"h{h}_eidx_{pos}" (.bitVector expLutBits)
      if scoreBits > expLutBits then
        let upperBits ← makeWire s!"h{h}_eup_{pos}" (.bitVector (scoreBits - expLutBits))
        emitAssign upperBits (Expr.slice (.ref absDiffWire) (scoreBits - 1) expLutBits)
        let isLarge ← makeWire s!"h{h}_elg_{pos}" (.bitVector 1)
        emitAssign isLarge (Expr.op .not [Expr.op .eq [.ref upperBits, .const 0 (scoreBits - expLutBits)]])
        let lowBits ← makeWire s!"h{h}_elo_{pos}" (.bitVector expLutBits)
        emitAssign lowBits (Expr.slice (.ref absDiffWire) (expLutBits - 1) 0)
        emitAssign idxWire (Expr.mux (.ref isLarge) (.const 255 expLutBits) (.ref lowBits))
      else
        emitAssign idxWire (Expr.slice (.ref absDiffWire) (expLutBits - 1) 0)

      let expResult ← buildLUTMuxTree expLUT (.ref idxWire) expLutBits softmaxTotalBits s!"h{h}_exp_{pos}"
      expVals := expVals.push expResult

    let expSum ← buildAdderTree expVals 0 noPipelineCfg

    let recipLUT := generateRecipLUT expSum.width
    let recipIdx ← makeWire s!"h{h}_ridx" (.bitVector recipLutBits)
    if expSum.width > recipLutBits then
      emitAssign recipIdx (Expr.slice expSum.expr (expSum.width - 1) (expSum.width - recipLutBits))
    else
      emitAssign recipIdx (Expr.slice expSum.expr (recipLutBits - 1) 0)

    let recipVal ← buildLUTMuxTree recipLUT (.ref recipIdx) recipLutBits softmaxTotalBits s!"h{h}_recip"

    -- Normalize weights
    let mulWidth := softmaxTotalBits * 2
    let mut weightRefs : Array SizedExpr := #[]
    for pos in [:config.seqLen] do
      let expExt ← signExtendExpr expVals[pos]! mulWidth
      let recipExt ← signExtendExpr recipVal mulWidth
      let prodWire ← makeWire s!"h{h}_nprod_{pos}" (.bitVector mulWidth)
      emitAssign prodWire (Expr.mul expExt.expr recipExt.expr)
      let shiftWire ← makeWire s!"h{h}_nshift_{pos}" (.bitVector mulWidth)
      emitAssign shiftWire (Expr.op .asr [.ref prodWire, .const softmaxFracBits mulWidth])
      let weightWire ← makeWire s!"h{h}_wt_{pos}" (.bitVector softmaxTotalBits)
      emitAssign weightWire (Expr.slice (.ref shiftWire) (softmaxTotalBits - 1) 0)
      weightRefs := weightRefs.push { expr := .ref weightWire, width := softmaxTotalBits }

    -- Score-V multiply for this head
    let svMulWidth := 40
    for j in [:config.headDim] do
      let mut products : Array SizedExpr := #[]
      for pos in [:config.seqLen] do
        let vRef : SizedExpr := { expr := .ref s!"v_cache_h{h}_{pos}_{j}", width := qkvBits }
        let vExt ← signExtendExpr vRef svMulWidth
        let wExt ← signExtendExpr weightRefs[pos]! svMulWidth
        let prodWire ← makeWire s!"h{h}_sv_{j}_{pos}" (.bitVector svMulWidth)
        emitAssign prodWire (Expr.mul wExt.expr vExt.expr)
        products := products.push { expr := .ref prodWire, width := svMulWidth }

      let sum ← buildAdderTree products 0 noPipelineCfg
      let shiftWire ← makeWire s!"h{h}_svs_{j}" (.bitVector sum.width)
      emitAssign shiftWire (Expr.op .asr [sum.expr, .const softmaxFracBits sum.width])
      let outWire ← makeWire s!"h{h}_out_{j}" (.bitVector softmaxTotalBits)
      emitAssign outWire (Expr.slice (.ref shiftWire) (softmaxTotalBits - 1) 0)
      concatOutputs := concatOutputs.push { expr := .ref outWire, width := softmaxTotalBits }

  -- ==========================================
  -- Concatenation + Output Projection
  -- ==========================================
  -- concatOutputs has nHeads × headDim elements (Q8.24 / 32-bit each)
  -- Output projection: BitLinear row for each output element
  let modelDim := outProjWeights.size

  for row in [:modelDim] do
    let rowWeights := outProjWeights[row]!
    -- Each concat element is 32-bit; apply ternary weights
    let mut macs : Array SizedExpr := #[]
    for i in [:rowWeights.size] do
      let w := rowWeights[i]!
      if i < concatOutputs.size then
        if w == 1 then
          macs := macs.push concatOutputs[i]!
        else if w == -1 then
          let negWire ← makeWire s!"oproj_neg_{row}_{i}" (.bitVector softmaxTotalBits)
          emitAssign negWire (Expr.sub (.const 0 softmaxTotalBits) concatOutputs[i]!.expr)
          macs := macs.push { expr := .ref negWire, width := softmaxTotalBits }

    if macs.size == 0 then
      addOutput s!"mha_out_{row}" (.bitVector softmaxTotalBits)
      emitAssign s!"mha_out_{row}" (.const 0 softmaxTotalBits)
    else
      let sum ← buildAdderTree macs 0 noPipelineCfg

      -- Apply scale
      let outScale := if h : row < outProjScales.size then outProjScales[row]
        else (2^scaleFracBits : Nat)
      let accExt ← signExtendExpr sum mulProductBits
      let scaledProd ← makeWire s!"oproj_prod_{row}" (.bitVector mulProductBits)
      emitAssign scaledProd (Expr.mul accExt.expr (.const outScale mulProductBits))
      let scaledShift ← makeWire s!"oproj_shift_{row}" (.bitVector mulProductBits)
      emitAssign scaledShift (Expr.op .asr [.ref scaledProd, .const scaleFracBits mulProductBits])
      let resultWire ← makeWire s!"oproj_result_{row}" (.bitVector softmaxTotalBits)
      emitAssign resultWire (Expr.slice (.ref scaledShift) (softmaxTotalBits - 1) 0)

      addOutput s!"mha_out_{row}" (.bitVector softmaxTotalBits)
      emitAssign s!"mha_out_{row}" (.ref resultWire)

/-- Build a standalone multi-head attention module -/
def buildMultiHeadAttention
    (config : MultiHeadConfig)
    (allQWeights allKWeights allVWeights : Array (Array (Array Int)))
    (allQScales allKScales allVScales : Array (Array Int))
    (outProjWeights : Array (Array Int))
    (outProjScales : Array Int)
    (cfg : GeneratorConfig) : Module :=
  CircuitM.runModule s!"MultiHeadAttention_{config.nHeads}h_{config.headDim}d" do
    generateMultiHeadAttention config allQWeights allKWeights allVWeights
      allQScales allKScales allVScales outProjWeights outProjScales cfg

end Sparkle.Examples.BitNet.Attention
