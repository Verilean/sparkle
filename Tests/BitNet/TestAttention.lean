/-
  Hespera Attention Tests

  Unit tests for the attention datapath:
  - INT8 quantization (spec + RTL structure)
  - Q·K^T dot product (spec + RTL structure)
  - QKV projection (RTL structure)
  - Full attention head pipeline (end-to-end RTL)
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.Verilog
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.Attention.Quantize
import Examples.BitNet.Attention.DotProduct
import Examples.BitNet.Attention.QKVProjection
import Examples.BitNet.Attention.Softmax
import Examples.BitNet.Attention.ScoreVMul
import Examples.BitNet.Attention.MultiHead
import Examples.BitNet.Attention.Top

namespace Sparkle.Examples.BitNet.Tests.Attention

open Sparkle.Examples.BitNet
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

/-- Simple test harness -/
def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  PASS: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"

-- ============================================================================
-- Quantization Spec Tests
-- ============================================================================

def testQuantizeSpec : IO Unit := do
  IO.println "--- Quantize INT8 Spec Tests ---"

  -- 1.0 (Q16.16 = 0x10000 = 65536), shift 10 → 65536/1024 = 64
  check "quant: 1.0 shift10 → 64"
    (quantizeToInt8 (BitVec.ofNat 32 0x10000) 10 == BitVec.ofInt 8 64)

  -- -1.0, shift 10 → -64
  check "quant: -1.0 shift10 → -64"
    (quantizeToInt8 (BitVec.ofInt 32 (-0x10000)) 10 == BitVec.ofInt 8 (-64))

  -- 0.0 → 0
  check "quant: 0 → 0"
    (quantizeToInt8 (BitVec.ofNat 32 0) 10 == BitVec.ofInt 8 0)

  -- Positive saturation: very large → 127
  check "quant: pos overflow → 127"
    (quantizeToInt8 (BitVec.ofNat 32 0x7FFFFFFF) 10 == BitVec.ofNat 8 127)

  -- Negative saturation: very negative → -128
  check "quant: neg overflow → -128"
    (quantizeToInt8 (BitVec.ofInt 32 (-0x7FFFFFFF)) 10 == BitVec.ofInt 8 (-128))

  -- 0.5 (Q16.16 = 0x8000), shift 10 → 32
  check "quant: 0.5 shift10 → 32"
    (quantizeToInt8 (BitVec.ofNat 32 0x8000) 10 == BitVec.ofInt 8 32)

-- ============================================================================
-- INT8 Dot Product Spec Tests
-- ============================================================================

def testDotProductSpec : IO Unit := do
  IO.println "--- INT8 Dot Product Spec Tests ---"

  -- dot([1, 2, 3], [4, 5, 6]) = 4 + 10 + 18 = 32
  check "dot: [1,2,3]·[4,5,6] = 32"
    (int8DotProduct
      #[BitVec.ofInt 8 1, BitVec.ofInt 8 2, BitVec.ofInt 8 3]
      #[BitVec.ofInt 8 4, BitVec.ofInt 8 5, BitVec.ofInt 8 6]
      == 32)

  -- dot([1, 0, -1], [1, 1, 1]) = 0
  check "dot: [1,0,-1]·[1,1,1] = 0"
    (int8DotProduct
      #[BitVec.ofInt 8 1, BitVec.ofInt 8 0, BitVec.ofInt 8 (-1)]
      #[BitVec.ofInt 8 1, BitVec.ofInt 8 1, BitVec.ofInt 8 1]
      == 0)

  -- dot([-128], [127]) = -16256
  check "dot: [-128]·[127] = -16256"
    (int8DotProduct
      #[BitVec.ofInt 8 (-128)]
      #[BitVec.ofInt 8 127]
      == -16256)

  -- dot([10, 20], [3, 4]) = 30 + 80 = 110
  check "dot: [10,20]·[3,4] = 110"
    (int8DotProduct
      #[BitVec.ofInt 8 10, BitVec.ofInt 8 20]
      #[BitVec.ofInt 8 3, BitVec.ofInt 8 4]
      == 110)

  -- Scaled score: dot([8,8],[8,8]) / 2^3 = 128/8 = 16
  check "scaled: [8,8]·[8,8] / 8 = 16"
    (scaledScore
      #[BitVec.ofInt 8 8, BitVec.ofInt 8 8]
      #[BitVec.ofInt 8 8, BitVec.ofInt 8 8]
      3 == 16)

  -- Empty dot product = 0
  check "dot: []·[] = 0"
    (int8DotProduct #[] #[] == 0)

-- ============================================================================
-- Quantize RTL Structure Tests
-- ============================================================================

def testQuantizeRTL : IO Unit := do
  IO.println "--- Quantize RTL Tests ---"

  let m := Sparkle.Examples.BitNet.Attention.buildQuantize 10

  check "quantize: 1 input (x)" (m.inputs.length == 1)
  check "quantize: 1 output (q)" (m.outputs.length == 1)
  check "quantize: input is 32-bit"
    (m.inputs.head?.map (·.ty) == some (.bitVector 32))
  check "quantize: output is 8-bit"
    (m.outputs.head?.map (·.ty) == some (.bitVector 8))
  check "quantize: module named correctly"
    (m.name == "QuantizeInt8_shift10")

  let verilog := toVerilog m
  check "quantize: non-empty Verilog" (verilog.length > 50)
  IO.println ""
  IO.println "  --- Quantize Verilog ---"
  IO.println verilog

-- ============================================================================
-- DotProduct RTL Structure Tests
-- ============================================================================

def testDotProductRTL : IO Unit := do
  IO.println "--- Q·K^T Dot Product RTL Tests ---"

  -- Test with headDim=4, scaleDkShift=1 (small for testing)
  let cfg : GeneratorConfig := { baseBitWidth := 8, pipelineEvery := 0 }
  let m := Sparkle.Examples.BitNet.Attention.buildDotProduct 4 1 cfg

  -- Inputs: clk + rst + 4 q + 4 k = 10
  check "dotprod: 10 inputs (clk+rst+4q+4k)" (m.inputs.length == 10)
  check "dotprod: 1 output (score)" (m.outputs.length == 1)
  check "dotprod: module named QK_DotProduct_4elem"
    (m.name == "QK_DotProduct_4elem")

  -- Check q/k input names and widths
  let qInputs := m.inputs.filter (fun p => p.name.startsWith "q_")
  let kInputs := m.inputs.filter (fun p => p.name.startsWith "k_")
  check "dotprod: 4 q inputs" (qInputs.length == 4)
  check "dotprod: 4 k inputs" (kInputs.length == 4)
  check "dotprod: all q are 8-bit" (qInputs.all (fun p => p.ty == .bitVector 8))
  check "dotprod: all k are 8-bit" (kInputs.all (fun p => p.ty == .bitVector 8))

  -- Output width: productBits(16) + ceil(log2(4))=2 levels → 18 bits
  check "dotprod: output is 18-bit"
    (m.outputs.head?.map (·.ty) == some (.bitVector 18))

  let verilog := toVerilog m
  check "dotprod: non-empty Verilog" (verilog.length > 100)
  IO.println ""
  IO.println "  --- DotProduct Verilog (headDim=4) ---"
  IO.println verilog

-- ============================================================================
-- DotProduct with Pipeline Registers
-- ============================================================================

def testDotProductPipelined : IO Unit := do
  IO.println "--- Q·K^T Pipelined DotProduct Tests ---"

  let cfg : GeneratorConfig := { baseBitWidth := 8, pipelineEvery := 1 }
  let m := Sparkle.Examples.BitNet.Attention.buildDotProduct 8 3 cfg

  -- 8-element dot product with pipeline every level
  check "pipelined: module name" (m.name == "QK_DotProduct_8elem")
  check "pipelined: 18 inputs (clk+rst+8q+8k)" (m.inputs.length == 18)

  -- Check pipeline registers exist
  let regCount := m.body.foldl (fun acc s =>
    match s with
    | .register .. => acc + 1
    | _ => acc) 0
  check "pipelined: has pipeline registers" (regCount > 0)
  IO.println s!"  INFO: {regCount} pipeline registers inserted"

-- ============================================================================
-- QKV Projection RTL Tests
-- ============================================================================

def testQKVProjectionRTL : IO Unit := do
  IO.println "--- QKV Projection RTL Tests ---"

  -- Small test: headDim=2, inDim=4
  let qW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]

  -- Q8.24 scale factors: all 1.0 = 0x01000000
  let scales : Array Int := #[0x01000000, 0x01000000]

  let cfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }
  let m := Sparkle.Examples.BitNet.Attention.buildQKVProjection qW kW vW scales scales scales 10 cfg

  check "qkv: module named QKV_Projection_2head"
    (m.name == "QKV_Projection_2head")

  -- Inputs: clk + rst + 4 x = 6
  let xInputs := m.inputs.filter (fun p => p.name.startsWith "x_")
  check "qkv: 4 activation inputs" (xInputs.length == 4)

  -- Outputs: 2 q + 2 k + 2 v = 6
  check "qkv: 6 outputs (2q + 2k + 2v)" (m.outputs.length == 6)

  -- All outputs are 8-bit INT8
  check "qkv: all outputs are 8-bit"
    (m.outputs.all (fun p => p.ty == .bitVector 8))

  let verilog := toVerilog m
  check "qkv: non-empty Verilog" (verilog.length > 200)

-- ============================================================================
-- Full Attention Head Pipeline Tests
-- ============================================================================

def testAttentionHeadRTL : IO Unit := do
  IO.println "--- Full Attention Head Pipeline Tests ---"

  -- Small test: headDim=2, inDim=4
  let qW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let scales : Array Int := #[0x01000000, 0x01000000]

  let headCfg : Sparkle.Examples.BitNet.Attention.AttentionHeadConfig := {
    headDim := 2
    inDim := 4
    quantShift := 10
    dkShift := 1  -- simple shift for testing
  }
  let cfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }

  let m := Sparkle.Examples.BitNet.Attention.buildAttentionHead headCfg qW kW vW
    scales scales scales cfg

  check "attn: module named AttentionHead_2dim"
    (m.name == "AttentionHead_2dim")

  -- Inputs: clk + rst + 4 x = 6
  check "attn: 6 inputs (clk+rst+4x)" (m.inputs.length == 6)

  -- Outputs: score + 2 v = 3
  let scoreOutputs := m.outputs.filter (fun p => p.name == "score")
  let vOutputs := m.outputs.filter (fun p => p.name.startsWith "v_")
  check "attn: 1 score output" (scoreOutputs.length == 1)
  check "attn: 2 v outputs" (vOutputs.length == 2)

  -- V outputs are 8-bit
  check "attn: v outputs are 8-bit"
    (vOutputs.all (fun p => p.ty == .bitVector 8))

  -- No FSM (no register statements from state machine)
  let hasStateMachine := m.wires.any (fun p =>
    p.name.find? "state" |>.isSome)
  check "attn: no FSM state machine" (!hasStateMachine)

  let verilog := toVerilog m
  check "attn: non-empty Verilog" (verilog.length > 300)
  IO.println ""
  IO.println "  --- Attention Head Verilog (headDim=2, inDim=4) ---"
  IO.println verilog

-- ============================================================================
-- Softmax Spec Tests
-- ============================================================================

def testSoftmaxSpec : IO Unit := do
  IO.println "--- Softmax Spec Tests ---"

  -- maxScore correctness
  check "maxScore: [3,1,4,1] = 4" (maxScore #[3, 1, 4, 1] == 4)
  check "maxScore: [-5,-3,-1] = -1" (maxScore #[-5, -3, -1] == -1)
  check "maxScore: [7,7,7] = 7" (maxScore #[7, 7, 7] == 7)
  check "maxScore: [42] = 42" (maxScore #[42] == 42)

  -- expQ8_24 basic checks
  check "exp(0) = 2^24" (expQ8_24 0 == (2^softmaxFracBits : Nat))
  check "exp(-1) < 2^24" (expQ8_24 (-1) < (2^softmaxFracBits : Nat))
  check "exp(-1) > 0" (expQ8_24 (-1) > 0)

  -- softmaxRef: equal scores → equal weights
  let ws := softmaxRef #[5, 5, 5, 5]
  check "softmax: 4 weights" (ws.size == 4)
  check "softmax: equal inputs → equal weights" (ws[0]! == ws[1]! && ws[1]! == ws[2]! && ws[2]! == ws[3]!)

  -- softmaxRef: all weights positive
  let wsPos := softmaxRef #[1, 2, 3, 4]
  check "softmax: all positive" (wsPos.all (· > 0))

  -- softmaxRef: weights sum approximately to 2^24
  let total := wsPos.foldl (· + ·) 0
  let oneQ8_24 : Int := (2^softmaxFracBits : Nat)
  -- Allow 1% tolerance
  let tolerance := oneQ8_24 / 100
  check "softmax: sum ≈ 2^24" (total > oneQ8_24 - tolerance && total < oneQ8_24 + tolerance)

-- ============================================================================
-- Softmax RTL Structure Tests
-- ============================================================================

def testSoftmaxRTL : IO Unit := do
  IO.println "--- Softmax RTL Tests ---"

  -- seqLen=4, scoreBits=18
  let m := Sparkle.Examples.BitNet.Attention.buildSoftmax 4 18

  check "softmax: module named Softmax_4seq" (m.name == "Softmax_4seq")

  -- Inputs: 4 scores
  let scoreInputs := m.inputs.filter (fun p => p.name.startsWith "score_")
  check "softmax: 4 score inputs" (scoreInputs.length == 4)

  -- Outputs: 4 weights
  let weightOutputs := m.outputs.filter (fun p => p.name.startsWith "weight_")
  check "softmax: 4 weight outputs" (weightOutputs.length == 4)

  -- All outputs are 32-bit (Q8.24)
  check "softmax: all outputs 32-bit"
    (weightOutputs.all (fun p => p.ty == .bitVector 32))

  -- No FSM (combinational)
  let hasStateMachine := m.wires.any (fun p =>
    p.name.find? "state" |>.isSome)
  check "softmax: no FSM" (!hasStateMachine)

  let verilog := toVerilog m
  check "softmax: non-empty Verilog" (verilog.length > 100)

-- ============================================================================
-- Score-V Multiply RTL Tests
-- ============================================================================

def testScoreVMulRTL : IO Unit := do
  IO.println "--- Score-V Multiply RTL Tests ---"

  -- seqLen=4, headDim=2
  let m := Sparkle.Examples.BitNet.Attention.buildScoreVMul 4 2

  check "scoreVMul: module named ScoreVMul_4x2" (m.name == "ScoreVMul_4x2")

  -- Inputs: 4 weights (32-bit) + 4×2 V values (8-bit) = 12
  let weightInputs := m.inputs.filter (fun p => p.name.startsWith "weight_")
  let vInputs := m.inputs.filter (fun p => p.name.startsWith "v_")
  check "scoreVMul: 4 weight inputs" (weightInputs.length == 4)
  check "scoreVMul: 8 V inputs (4×2)" (vInputs.length == 8)

  -- Outputs: 2 (headDim)
  let outOutputs := m.outputs.filter (fun p => p.name.startsWith "out_")
  check "scoreVMul: 2 outputs" (outOutputs.length == 2)

  -- Output widths are 32-bit
  check "scoreVMul: outputs 32-bit"
    (outOutputs.all (fun p => p.ty == .bitVector 32))

  let verilog := toVerilog m
  check "scoreVMul: non-empty Verilog" (verilog.length > 100)

-- ============================================================================
-- Full Attention Head (with softmax + V output) Tests
-- ============================================================================

def testFullAttentionHeadRTL : IO Unit := do
  IO.println "--- Full Attention Head (softmax+V) Tests ---"

  let qW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let scales : Array Int := #[0x01000000, 0x01000000]

  let fullCfg : Sparkle.Examples.BitNet.Attention.FullAttentionConfig := {
    headDim := 2
    inDim := 4
    quantShift := 10
    dkShift := 1
    seqLen := 4
  }
  let cfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }

  let m := Sparkle.Examples.BitNet.Attention.buildFullAttentionHead fullCfg qW kW vW
    scales scales scales cfg

  check "fullAttn: module named correctly"
    (m.name == "FullAttentionHead_2dim_4seq")

  -- Inputs: clk + rst + 4 x + 4×2 k_cache + 4×2 v_cache = 2 + 4 + 8 + 8 = 22
  let xInputs := m.inputs.filter (fun p => p.name.startsWith "x_")
  check "fullAttn: has x inputs" (xInputs.length == 4)
  let kCacheInputs := m.inputs.filter (fun p => p.name.startsWith "k_cache_")
  check "fullAttn: has k_cache inputs" (kCacheInputs.length == 8)
  let vCacheInputs := m.inputs.filter (fun p => p.name.startsWith "v_cache_")
  check "fullAttn: has v_cache inputs" (vCacheInputs.length == 8)

  -- Outputs: 2 attn_out (headDim)
  let attnOutputs := m.outputs.filter (fun p => p.name.startsWith "attn_out_")
  check "fullAttn: 2 attention outputs" (attnOutputs.length == 2)
  check "fullAttn: outputs are 32-bit"
    (attnOutputs.all (fun p => p.ty == .bitVector 32))

  -- No FSM
  let hasStateMachine := m.wires.any (fun p =>
    p.name.find? "state" |>.isSome)
  check "fullAttn: no FSM" (!hasStateMachine)

  let verilog := toVerilog m
  check "fullAttn: non-empty Verilog" (verilog.length > 500)

-- ============================================================================
-- Multi-Head Attention Tests
-- ============================================================================

def testMultiHeadRTL : IO Unit := do
  IO.println "--- Multi-Head Attention Tests ---"

  -- nHeads=2, headDim=2, inDim=4, seqLen=4
  let mhaCfg : Sparkle.Examples.BitNet.Attention.MultiHeadConfig := {
    nHeads := 2
    headDim := 2
    inDim := 4
    seqLen := 4
    quantShift := 10
    dkShift := 1
  }

  -- Weights per head (2 heads × 2 rows × 4 cols)
  let qW0 : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW0 : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW0 : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let qW1 : Array (Array Int) := #[#[0, 1, 1, 0], #[1, 0, 0, -1]]
  let kW1 : Array (Array Int) := #[#[1, -1, 0, 0], #[0, 0, 1, 1]]
  let vW1 : Array (Array Int) := #[#[1, 0, -1, 0], #[0, 1, 0, -1]]

  let scales : Array Int := #[0x01000000, 0x01000000]

  let allQW := #[qW0, qW1]
  let allKW := #[kW0, kW1]
  let allVW := #[vW0, vW1]
  let allQS := #[scales, scales]
  let allKS := #[scales, scales]
  let allVS := #[scales, scales]

  -- Output projection: modelDim=4 rows × concatDim=4 cols (ternary)
  let outProjW : Array (Array Int) := #[
    #[1, -1, 0, 1],
    #[0, 1, 1, 0],
    #[-1, 0, 1, -1],
    #[1, 1, 0, 0]
  ]
  let outProjS : Array Int := #[0x01000000, 0x01000000, 0x01000000, 0x01000000]

  let cfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }

  let m := Sparkle.Examples.BitNet.Attention.buildMultiHeadAttention mhaCfg
    allQW allKW allVW allQS allKS allVS outProjW outProjS cfg

  check "mha: module named correctly"
    (m.name == "MultiHeadAttention_2h_2d")

  -- Outputs: 4 (modelDim = outProjWeights.size)
  let mhaOutputs := m.outputs.filter (fun p => p.name.startsWith "mha_out_")
  check "mha: 4 output elements" (mhaOutputs.length == 4)
  check "mha: outputs are 32-bit"
    (mhaOutputs.all (fun p => p.ty == .bitVector 32))

  -- Has x inputs
  let xInputs := m.inputs.filter (fun p => p.name.startsWith "x_")
  check "mha: 4 x inputs" (xInputs.length == 4)

  -- Has KV cache for both heads
  let kCacheInputs := m.inputs.filter (fun p => p.name.startsWith "k_cache_h")
  let vCacheInputs := m.inputs.filter (fun p => p.name.startsWith "v_cache_h")
  check "mha: 16 k_cache inputs (2 heads × 4 pos × 2 dim)"
    (kCacheInputs.length == 16)
  check "mha: 16 v_cache inputs (2 heads × 4 pos × 2 dim)"
    (vCacheInputs.length == 16)

  let verilog := toVerilog m
  check "mha: non-empty Verilog" (verilog.length > 1000)

def runAll : IO Unit := do
  IO.println "=== Attention Tests ==="
  IO.println ""
  testQuantizeSpec
  testDotProductSpec
  testSoftmaxSpec
  IO.println ""
  testQuantizeRTL
  testDotProductRTL
  testDotProductPipelined
  testQKVProjectionRTL
  testAttentionHeadRTL
  IO.println ""
  testSoftmaxRTL
  testScoreVMulRTL
  testFullAttentionHeadRTL
  testMultiHeadRTL
  IO.println ""
  IO.println "=== All attention tests complete ==="

end Sparkle.Examples.BitNet.Tests.Attention
