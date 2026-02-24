/-
  Sparkle Examples — BitNet Attention — Streaming Pipeline Top

  Connects the QKV Projection and Q·K^T Dot Product in a fully pipelined
  streaming datapath for one attention head.

  Pipeline:
    x[inDim] ──► QKV Projection ──► q[headDim] (INT8)  ──┐
                                 └─► k[headDim] (INT8)  ──┤
                                 └─► v[headDim] (INT8) ─► v_out
                                                          │
                                              Q·K^T DotProduct ──► score
                                              (INT8 multipliers
                                               + adder tree
                                               + 1/sqrt(d_k) scale)

  No FSM — pure pipelined datapath.
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

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.BitNet.BitLinear
open CircuitM

/-- Configuration for one attention head -/
structure AttentionHeadConfig where
  headDim      : Nat         -- Dimension per head (e.g., 64)
  inDim        : Nat         -- Input dimension (e.g., 2048)
  quantShift   : Nat := 10   -- Q16.16 → INT8 shift (1.0 → 64 in INT8)
  dkShift      : Nat := 3    -- 1/sqrt(d_k) = asr 3 for d_k=64
  deriving Repr, BEq

/-- Generate the complete attention head pipeline (inline, single module).

    Combines QKV projection + quantization + Q·K^T dot product.
    Everything is inlined into one big combinational/pipelined circuit.

    Inputs:  clk, rst, x_0..x_{inDim-1}[baseBitWidth-1:0]
    Outputs: score[scoreWidth-1:0],
             v_0..v_{headDim-1}[7:0]  (V values passed through for later use) -/
def generateAttentionHead
    (config : AttentionHeadConfig)
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (cfg : GeneratorConfig) : CircuitM Unit := do
  -- Shared activation inputs
  addInput cfg.clockName .bit
  addInput cfg.resetName .bit
  for i in [:config.inDim] do
    addInput s!"x_{i}" (.bitVector cfg.baseBitWidth)

  -- ==========================================
  -- Stage 1: QKV Projection (BitLinear → Scale → Quantize)
  -- ==========================================

  -- Q projection rows → INT8
  let mut qOutputs : Array SizedExpr := #[]
  for j in [:config.headDim] do
    let acc ← generateBitLinearRow s!"q_row{j}" qWeights[j]! cfg
    let qScale := if h : j < qScales.size then qScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc qScale
    let quantized ← generateQuantizeInt8 scaled config.quantShift
    -- Wire to q_j for the dot product stage
    let qWire ← makeWire s!"q_{j}" (.bitVector qkvBits)
    emitAssign qWire quantized.expr
    qOutputs := qOutputs.push { expr := .ref qWire, width := qkvBits }

  -- K projection rows → INT8
  let mut kOutputs : Array SizedExpr := #[]
  for j in [:config.headDim] do
    let acc ← generateBitLinearRow s!"k_row{j}" kWeights[j]! cfg
    let kScale := if h : j < kScales.size then kScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc kScale
    let quantized ← generateQuantizeInt8 scaled config.quantShift
    let kWire ← makeWire s!"k_{j}" (.bitVector qkvBits)
    emitAssign kWire quantized.expr
    kOutputs := kOutputs.push { expr := .ref kWire, width := qkvBits }

  -- V projection rows → INT8 (pass through to output)
  for j in [:config.headDim] do
    let acc ← generateBitLinearRow s!"v_row{j}" vWeights[j]! cfg
    let vScale := if h : j < vScales.size then vScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc vScale
    let quantized ← generateQuantizeInt8 scaled config.quantShift
    addOutput s!"v_{j}" (.bitVector qkvBits)
    emitAssign s!"v_{j}" quantized.expr

  -- ==========================================
  -- Stage 2: Q·K^T Dot Product (INT8 multipliers + adder tree)
  -- ==========================================

  -- Multiplier array: sign-extend to 16 bits, multiply
  let mut products : Array SizedExpr := #[]
  for i in [:config.headDim] do
    let qExt ← signExtendExpr qOutputs[i]! productBits
    let kExt ← signExtendExpr kOutputs[i]! productBits
    let prodWire ← makeWire s!"qk_prod_{i}" (.bitVector productBits)
    emitAssign prodWire (Expr.mul qExt.expr kExt.expr)
    products := products.push { expr := .ref prodWire, width := productBits }

  if products.size == 0 then
    addOutput "score" (.bitVector productBits)
    emitAssign "score" (.const 0 productBits)
    return

  -- Adder tree reduction
  let dotSum ← buildAdderTree products 0 cfg

  -- ==========================================
  -- Stage 3: Scale by 1/sqrt(d_k)
  -- ==========================================

  if config.dkShift > 0 then
    let scoreWire ← makeWire "score_scaled" (.bitVector dotSum.width)
    emitAssign scoreWire (Expr.op .asr [dotSum.expr, .const config.dkShift dotSum.width])
    addOutput "score" (.bitVector dotSum.width)
    emitAssign "score" (.ref scoreWire)
  else
    addOutput "score" (.bitVector dotSum.width)
    emitAssign "score" dotSum.expr

/-- Build a standalone attention head module -/
def buildAttentionHead
    (config : AttentionHeadConfig)
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (cfg : GeneratorConfig) : Module :=
  CircuitM.runModule s!"AttentionHead_{config.headDim}dim" do
    generateAttentionHead config qWeights kWeights vWeights
      qScales kScales vScales cfg

/-- Configuration for a full attention head with KV cache -/
structure FullAttentionConfig extends AttentionHeadConfig where
  seqLen : Nat  -- Number of cached KV positions
  deriving Repr, BEq

/-- Generate a full attention head with softmax and weighted V output.

    Pipeline:
    1. QKV Projection (for current token query only)
    2. Dot product Q·K^T for each cached K position → seqLen scores
    3. Softmax over scores → seqLen Q8.24 weights
    4. Score-V multiply → headDim output values

    Inputs:  clk, rst, x_0..x_{inDim-1}[baseBitWidth-1:0],
             k_cache_{i}_{j}[7:0], v_cache_{i}_{j}[7:0]
    Outputs: attn_out_0..attn_out_{headDim-1}[31:0]

    All inlined, fully combinational for small demo sizes. -/
def generateFullAttentionHead
    (config : FullAttentionConfig)
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (cfg : GeneratorConfig) : CircuitM Unit := do
  -- ==========================================
  -- Input declarations
  -- ==========================================
  addInput cfg.clockName .bit
  addInput cfg.resetName .bit
  for i in [:config.inDim] do
    addInput s!"x_{i}" (.bitVector cfg.baseBitWidth)

  -- KV cache inputs
  for i in [:config.seqLen] do
    for j in [:config.headDim] do
      addInput s!"k_cache_{i}_{j}" (.bitVector qkvBits)
  for i in [:config.seqLen] do
    for j in [:config.headDim] do
      addInput s!"v_cache_{i}_{j}" (.bitVector qkvBits)

  -- ==========================================
  -- Stage 1: QKV Projection (query only for inference)
  -- ==========================================
  let mut qOutputs : Array SizedExpr := #[]
  for j in [:config.headDim] do
    let acc ← generateBitLinearRow s!"q_row{j}" qWeights[j]! cfg
    let qScale := if h : j < qScales.size then qScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc qScale
    let quantized ← generateQuantizeInt8 scaled config.quantShift
    let qWire ← makeWire s!"q_{j}" (.bitVector qkvBits)
    emitAssign qWire quantized.expr
    qOutputs := qOutputs.push { expr := .ref qWire, width := qkvBits }

  -- Also project K and V for the current token (stored as position 0 in cache
  -- conceptually, but for this demo the cache is provided as inputs)
  -- K projection (for current token — not used if cache is pre-filled)
  for j in [:config.headDim] do
    let acc ← generateBitLinearRow s!"k_row{j}" kWeights[j]! cfg
    let kScale := if h : j < kScales.size then kScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc kScale
    let quantized ← generateQuantizeInt8 scaled config.quantShift
    let kWire ← makeWire s!"k_cur_{j}" (.bitVector qkvBits)
    emitAssign kWire quantized.expr

  -- V projection (for current token)
  for j in [:config.headDim] do
    let acc ← generateBitLinearRow s!"v_row{j}" vWeights[j]! cfg
    let vScale := if h : j < vScales.size then vScales[j] else (2^scaleFracBits : Nat)
    let scaled ← generateScaleConst acc vScale
    let quantized ← generateQuantizeInt8 scaled config.quantShift
    let vWire ← makeWire s!"v_cur_{j}" (.bitVector qkvBits)
    emitAssign vWire quantized.expr

  -- ==========================================
  -- Stage 2: Q·K^T dot products (one per cached K position)
  -- ==========================================
  let mut scores : Array SizedExpr := #[]
  for pos in [:config.seqLen] do
    -- Compute dot(q, K[pos]) using INT8 multipliers + adder tree
    let mut products : Array SizedExpr := #[]
    for j in [:config.headDim] do
      let qExt ← signExtendExpr qOutputs[j]! productBits
      let kRef : SizedExpr := { expr := .ref s!"k_cache_{pos}_{j}", width := qkvBits }
      let kExt ← signExtendExpr kRef productBits
      let prodWire ← makeWire s!"qk_prod_{pos}_{j}" (.bitVector productBits)
      emitAssign prodWire (Expr.mul qExt.expr kExt.expr)
      products := products.push { expr := .ref prodWire, width := productBits }

    if products.size == 0 then
      let zeroWire ← makeWire s!"score_{pos}" (.bitVector productBits)
      emitAssign zeroWire (.const 0 productBits)
      scores := scores.push { expr := .ref zeroWire, width := productBits }
    else
      let dotSum ← buildAdderTree products 0 cfg

      -- Scale by 1/sqrt(d_k)
      if config.dkShift > 0 then
        let scoreWire ← makeWire s!"score_{pos}" (.bitVector dotSum.width)
        emitAssign scoreWire (Expr.op .asr [dotSum.expr, .const config.dkShift dotSum.width])
        scores := scores.push { expr := .ref scoreWire, width := dotSum.width }
      else
        let scoreWire ← makeWire s!"score_{pos}" (.bitVector dotSum.width)
        emitAssign scoreWire dotSum.expr
        scores := scores.push { expr := .ref scoreWire, width := dotSum.width }

  -- Determine score bit width (all should be same width)
  let scoreBits := if scores.size > 0 then scores[0]!.width else productBits

  -- ==========================================
  -- Stage 3: Softmax over scores
  -- ==========================================

  -- Wire scores to softmax inputs
  let mut softmaxInputs : Array SizedExpr := #[]
  for pos in [:config.seqLen] do
    let smInWire ← makeWire s!"sm_in_{pos}" (.bitVector scoreBits)
    emitAssign smInWire scores[pos]!.expr
    softmaxInputs := softmaxInputs.push { expr := .ref smInWire, width := scoreBits }

  -- Max reduction
  let maxVal ← buildMaxTree softmaxInputs 0

  -- Subtract max and exp LUT
  let expLUT := generateExpLUT
  let mut expVals : Array SizedExpr := #[]
  for pos in [:config.seqLen] do
    let diffWire ← makeWire s!"sm_diff_{pos}" (.bitVector scoreBits)
    emitAssign diffWire (Expr.sub softmaxInputs[pos]!.expr maxVal.expr)

    let absDiffWire ← makeWire s!"sm_abs_{pos}" (.bitVector scoreBits)
    emitAssign absDiffWire (Expr.sub (.const 0 scoreBits) (.ref diffWire))

    let idxWire ← makeWire s!"sm_idx_{pos}" (.bitVector expLutBits)
    if scoreBits > expLutBits then
      let upperBits ← makeWire s!"sm_upper_{pos}" (.bitVector (scoreBits - expLutBits))
      emitAssign upperBits (Expr.slice (.ref absDiffWire) (scoreBits - 1) expLutBits)
      let isLarge ← makeWire s!"sm_large_{pos}" (.bitVector 1)
      emitAssign isLarge (Expr.op .not [Expr.op .eq [.ref upperBits, .const 0 (scoreBits - expLutBits)]])
      let lowBits ← makeWire s!"sm_low_{pos}" (.bitVector expLutBits)
      emitAssign lowBits (Expr.slice (.ref absDiffWire) (expLutBits - 1) 0)
      emitAssign idxWire (Expr.mux (.ref isLarge) (.const 255 expLutBits) (.ref lowBits))
    else
      emitAssign idxWire (Expr.slice (.ref absDiffWire) (expLutBits - 1) 0)

    let expResult ← buildLUTMuxTree expLUT (.ref idxWire) expLutBits softmaxTotalBits s!"sm_exp_{pos}"
    expVals := expVals.push expResult

  -- Sum exp values
  let noPipelineCfg : GeneratorConfig := {
    baseBitWidth := softmaxTotalBits
    pipelineEvery := 0
  }
  let expSum ← buildAdderTree expVals 0 noPipelineCfg

  -- Reciprocal LUT
  let recipLUT := generateRecipLUT expSum.width
  let recipIdx ← makeWire "sm_recip_idx" (.bitVector recipLutBits)
  if expSum.width > recipLutBits then
    emitAssign recipIdx (Expr.slice expSum.expr (expSum.width - 1) (expSum.width - recipLutBits))
  else
    emitAssign recipIdx (Expr.slice expSum.expr (recipLutBits - 1) 0)

  let recipVal ← buildLUTMuxTree recipLUT (.ref recipIdx) recipLutBits softmaxTotalBits "sm_recip"

  -- Normalize to get weights
  let mulWidth := softmaxTotalBits * 2  -- 64-bit product
  let mut weightRefs : Array SizedExpr := #[]
  for pos in [:config.seqLen] do
    let expExt ← signExtendExpr expVals[pos]! mulWidth
    let recipExt ← signExtendExpr recipVal mulWidth
    let prodWire ← makeWire s!"sm_nprod_{pos}" (.bitVector mulWidth)
    emitAssign prodWire (Expr.mul expExt.expr recipExt.expr)
    let shiftWire ← makeWire s!"sm_nshift_{pos}" (.bitVector mulWidth)
    emitAssign shiftWire (Expr.op .asr [.ref prodWire, .const softmaxFracBits mulWidth])
    let weightWire ← makeWire s!"attn_weight_{pos}" (.bitVector softmaxTotalBits)
    emitAssign weightWire (Expr.slice (.ref shiftWire) (softmaxTotalBits - 1) 0)
    weightRefs := weightRefs.push { expr := .ref weightWire, width := softmaxTotalBits }

  -- ==========================================
  -- Stage 4: Score-V Multiply (weighted V output)
  -- ==========================================
  let svMulWidth := 40  -- 2^24 × 128 < 2^31 < 2^39

  for j in [:config.headDim] do
    let mut products : Array SizedExpr := #[]
    for pos in [:config.seqLen] do
      let vRef : SizedExpr := { expr := .ref s!"v_cache_{pos}_{j}", width := qkvBits }
      let vExt ← signExtendExpr vRef svMulWidth
      let wExt ← signExtendExpr weightRefs[pos]! svMulWidth
      let prodWire ← makeWire s!"sv_prod_{j}_{pos}" (.bitVector svMulWidth)
      emitAssign prodWire (Expr.mul wExt.expr vExt.expr)
      products := products.push { expr := .ref prodWire, width := svMulWidth }

    let sum ← buildAdderTree products 0 noPipelineCfg
    let shiftWire ← makeWire s!"sv_shift_{j}" (.bitVector sum.width)
    emitAssign shiftWire (Expr.op .asr [sum.expr, .const softmaxFracBits sum.width])
    let outWire ← makeWire s!"attn_result_{j}" (.bitVector softmaxTotalBits)
    emitAssign outWire (Expr.slice (.ref shiftWire) (softmaxTotalBits - 1) 0)

    addOutput s!"attn_out_{j}" (.bitVector softmaxTotalBits)
    emitAssign s!"attn_out_{j}" (.ref outWire)

/-- Build a standalone full attention head module -/
def buildFullAttentionHead
    (config : FullAttentionConfig)
    (qWeights kWeights vWeights : Array (Array Int))
    (qScales kScales vScales : Array Int)
    (cfg : GeneratorConfig) : Module :=
  CircuitM.runModule s!"FullAttentionHead_{config.headDim}dim_{config.seqLen}seq" do
    generateFullAttentionHead config qWeights kWeights vWeights
      qScales kScales vScales cfg

end Sparkle.Examples.BitNet.Attention
