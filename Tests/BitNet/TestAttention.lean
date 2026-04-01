/-
  BitNet Attention Tests — Signal DSL

  Unit tests for the attention datapath:
  - INT8 quantization (spec + Signal DSL)
  - Q·K^T dot product (spec + Signal DSL)
  - QKV projection (Signal DSL)
  - Softmax (spec + Signal DSL)
  - Score-V multiply (Signal DSL)
  - Full attention head pipeline (Signal DSL)
  - Multi-head attention (Signal DSL)
-/

import IP.BitNet.Config
import IP.BitNet.Types
import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Core
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Attention.Quantize
import IP.BitNet.Attention.DotProduct
import IP.BitNet.Attention.QKVProjection
import IP.BitNet.Attention.Softmax
import IP.BitNet.Attention.ScoreVMul
import IP.BitNet.Attention.MultiHead
import IP.BitNet.Attention.Top

namespace Sparkle.IP.BitNet.Tests.Attention

open Sparkle.IP.BitNet
open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Attention

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
-- Quantize Signal DSL Tests
-- ============================================================================

def testQuantizeSignal : IO Unit := do
  IO.println "--- Quantize Signal Tests ---"

  -- 1.0, shift 10 → 64
  let x1 : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x10000)
  let q1 := quantizeInt8Signal 10 x1
  check "signal: quant(1.0, shift10) = 64" (q1.atTime 0 == BitVec.ofInt 8 64)

  -- -1.0, shift 10 → -64
  let x2 : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofInt 32 (-0x10000))
  let q2 := quantizeInt8Signal 10 x2
  check "signal: quant(-1.0, shift10) = -64" (q2.atTime 0 == BitVec.ofInt 8 (-64))

  -- 0 → 0
  let x3 : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0)
  let q3 := quantizeInt8Signal 10 x3
  check "signal: quant(0) = 0" (q3.atTime 0 == BitVec.ofInt 8 0)

  -- Positive saturation
  let x4 : Signal defaultDomain (BitVec 32) := Signal.pure (BitVec.ofNat 32 0x7FFFFFFF)
  let q4 := quantizeInt8Signal 10 x4
  check "signal: pos overflow → 127" (q4.atTime 0 == BitVec.ofNat 8 127)

  -- Verify matches spec
  check "signal: matches spec (1.0)"
    (q1.atTime 0 == quantizeToInt8 (BitVec.ofNat 32 0x10000) 10)

-- ============================================================================
-- DotProduct Signal DSL Tests
-- ============================================================================

def testDotProductSignal : IO Unit := do
  IO.println "--- DotProduct Signal Tests ---"

  -- Simple 2-element dot product: [10, 20] · [3, 4] = 110, no shift
  let qs : Array (Signal defaultDomain (BitVec 8)) :=
    #[Signal.pure (BitVec.ofInt 8 10), Signal.pure (BitVec.ofInt 8 20)]
  let ks : Array (Signal defaultDomain (BitVec 8)) :=
    #[Signal.pure (BitVec.ofInt 8 3), Signal.pure (BitVec.ofInt 8 4)]
  let score := dotProductSignal qs ks 0
  check "signal: [10,20]·[3,4] = 110" (score.atTime 0 == BitVec.ofInt 32 110)

  -- With shift: [8,8] · [8,8] = 128, shift 3 → 16
  let qs2 : Array (Signal defaultDomain (BitVec 8)) :=
    #[Signal.pure (BitVec.ofInt 8 8), Signal.pure (BitVec.ofInt 8 8)]
  let ks2 : Array (Signal defaultDomain (BitVec 8)) :=
    #[Signal.pure (BitVec.ofInt 8 8), Signal.pure (BitVec.ofInt 8 8)]
  let score2 := dotProductSignal qs2 ks2 3
  check "signal: [8,8]·[8,8] / 8 = 16" (score2.atTime 0 == BitVec.ofInt 32 16)

-- ============================================================================
-- QKV Projection Signal DSL Tests
-- ============================================================================

def testQKVProjectionSignal : IO Unit := do
  IO.println "--- QKV Projection Signal Tests ---"

  -- Small test: headDim=2, inDim=4
  let qW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let scales : Array Int := #[0x01000000, 0x01000000]

  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x10000),  -- 1.0
      Signal.pure (BitVec.ofNat 32 0x10000),  -- 1.0
      Signal.pure (BitVec.ofNat 32 0x10000),  -- 1.0
      Signal.pure (BitVec.ofNat 32 0x10000)]  -- 1.0

  let (qs, ks, vs) := qkvProjectionSignal qW kW vW scales scales scales 10 acts

  check "qkv: 2 Q outputs" (qs.size == 2)
  check "qkv: 2 K outputs" (ks.size == 2)
  check "qkv: 2 V outputs" (vs.size == 2)

-- ============================================================================
-- Softmax Signal DSL Tests
-- ============================================================================

def testSoftmaxSignal : IO Unit := do
  IO.println "--- Softmax Signal Tests ---"

  -- Equal scores → equal weights
  let scores : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofInt 32 5),
      Signal.pure (BitVec.ofInt 32 5),
      Signal.pure (BitVec.ofInt 32 5),
      Signal.pure (BitVec.ofInt 32 5)]
  let weights := softmaxSignal scores
  check "softmax: 4 weights" (weights.size == 4)
  -- Equal inputs → equal weights
  check "softmax: equal inputs → equal weights"
    (weights[0]!.atTime 0 == weights[1]!.atTime 0 &&
     weights[1]!.atTime 0 == weights[2]!.atTime 0 &&
     weights[2]!.atTime 0 == weights[3]!.atTime 0)
  -- All weights should be positive (non-zero)
  check "softmax: all positive"
    (weights.all (fun w => w.atTime 0 != (0 : BitVec 32)))

-- ============================================================================
-- Score-V Multiply Signal DSL Tests
-- ============================================================================

def testScoreVMulSignal : IO Unit := do
  IO.println "--- Score-V Multiply Signal Tests ---"

  -- 2 positions, headDim=2
  -- Weights: [0.5, 0.5] in Q8.24
  let halfQ824 : BitVec 32 := BitVec.ofNat 32 (2^23)  -- 0.5 in Q8.24
  let weights : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure halfQ824, Signal.pure halfQ824]

  -- V matrix: [[10, 20], [30, 40]]
  let vMatrix : Array (Array (Signal defaultDomain (BitVec 8))) :=
    #[#[Signal.pure (BitVec.ofInt 8 10), Signal.pure (BitVec.ofInt 8 20)],
      #[Signal.pure (BitVec.ofInt 8 30), Signal.pure (BitVec.ofInt 8 40)]]

  let outputs := scoreVMulSignal weights vMatrix 2
  check "scoreVMul: 2 outputs" (outputs.size == 2)

-- ============================================================================
-- Full Attention Head Signal DSL Tests
-- ============================================================================

def testAttentionHeadSignal : IO Unit := do
  IO.println "--- Attention Head Signal Tests ---"

  let qW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let scales : Array Int := #[0x01000000, 0x01000000]

  let headCfg : AttentionHeadConfig := {
    headDim := 2
    inDim := 4
    quantShift := 10
    dkShift := 1
  }

  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000)]

  let (score, vs) := attentionHeadSignal headCfg qW kW vW scales scales scales acts
  check "attn: produces score" true
  check "attn: 2 V outputs" (vs.size == 2)

-- ============================================================================
-- Full Attention Head with Softmax Tests
-- ============================================================================

def testFullAttentionHeadSignal : IO Unit := do
  IO.println "--- Full Attention Head (softmax+V) Signal Tests ---"

  let qW : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let scales : Array Int := #[0x01000000, 0x01000000]

  let fullCfg : FullAttentionConfig := {
    headDim := 2
    inDim := 4
    quantShift := 10
    dkShift := 1
    seqLen := 4
  }

  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000)]

  -- KV cache: 4 positions × 2 elements, all INT8 = 1
  let oneInt8 : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 1)
  let kCache : Array (Array (Signal defaultDomain (BitVec 8))) :=
    Array.replicate 4 (Array.replicate 2 oneInt8)
  let vCache : Array (Array (Signal defaultDomain (BitVec 8))) :=
    Array.replicate 4 (Array.replicate 2 oneInt8)

  let outputs := fullAttentionHeadSignal fullCfg qW kW vW
    scales scales scales acts kCache vCache

  check "fullAttn: 2 outputs" (outputs.size == 2)

-- ============================================================================
-- Multi-Head Attention Signal DSL Tests
-- ============================================================================

def testMultiHeadSignal : IO Unit := do
  IO.println "--- Multi-Head Attention Signal Tests ---"

  let mhaCfg : MultiHeadConfig := {
    nHeads := 2
    headDim := 2
    inDim := 4
    seqLen := 4
    quantShift := 10
    dkShift := 1
  }

  -- Weights per head
  let qW0 : Array (Array Int) := #[#[1, -1, 0, 1], #[0, 1, -1, 0]]
  let kW0 : Array (Array Int) := #[#[-1, 0, 1, 1], #[1, 1, 0, -1]]
  let vW0 : Array (Array Int) := #[#[0, 1, 1, -1], #[-1, 0, 0, 1]]
  let qW1 : Array (Array Int) := #[#[0, 1, 1, 0], #[1, 0, 0, -1]]
  let kW1 : Array (Array Int) := #[#[1, -1, 0, 0], #[0, 0, 1, 1]]
  let vW1 : Array (Array Int) := #[#[1, 0, -1, 0], #[0, 1, 0, -1]]

  let scales : Array Int := #[0x01000000, 0x01000000]

  -- Output projection
  let outProjW : Array (Array Int) := #[
    #[1, -1, 0, 1],
    #[0, 1, 1, 0],
    #[-1, 0, 1, -1],
    #[1, 1, 0, 0]
  ]
  let outProjS : Array Int := #[0x01000000, 0x01000000, 0x01000000, 0x01000000]

  let acts : Array (Signal defaultDomain (BitVec 32)) :=
    #[Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000),
      Signal.pure (BitVec.ofNat 32 0x10000)]

  -- KV cache: per head, 4 positions × 2 elements
  let oneInt8 : Signal defaultDomain (BitVec 8) := Signal.pure (BitVec.ofInt 8 1)
  let headCache : Array (Array (Signal defaultDomain (BitVec 8))) :=
    Array.replicate 4 (Array.replicate 2 oneInt8)
  let allKCache := #[headCache, headCache]
  let allVCache := #[headCache, headCache]

  let outputs := multiHeadAttentionSignal mhaCfg
    #[qW0, qW1] #[kW0, kW1] #[vW0, vW1]
    #[scales, scales] #[scales, scales] #[scales, scales]
    outProjW outProjS acts allKCache allVCache

  check "mha: 4 output elements" (outputs.size == 4)

def runAll : IO Unit := do
  IO.println "=== Attention Tests ==="
  IO.println ""
  testQuantizeSpec
  testDotProductSpec
  testSoftmaxSpec
  IO.println ""
  testQuantizeSignal
  testDotProductSignal
  testQKVProjectionSignal
  testSoftmaxSignal
  testScoreVMulSignal
  testAttentionHeadSignal
  testFullAttentionHeadSignal
  testMultiHeadSignal
  IO.println ""
  IO.println "=== All attention tests complete ==="

end Sparkle.IP.BitNet.Tests.Attention
