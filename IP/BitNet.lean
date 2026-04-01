/-
  Sparkle Examples — BitNet b1.58 Verified RTL Generator

  A ROM-fixed BitNet (ternary-weight) LLM inference core in synthesizable RTL,
  generated from Lean 4 via Sparkle HDL. Targets ASIC synthesis for BitNet b1.58 1B.
-/

import IP.BitNet.Config
import IP.BitNet.Types
import IP.BitNet.MemoryMap
import IP.BitNet.Primitives.Rom
import IP.BitNet.BitLinear.BitWidth
import IP.BitNet.BitLinear.Core
import IP.BitNet.BitLinear.Top
import IP.BitNet.BitLinear.Scale
import IP.BitNet.Layers.ReLUSq
import IP.BitNet.Layers.ResidualAdd
import IP.BitNet.Layers.ElemMul
import IP.BitNet.Layers.RMSNorm
import IP.BitNet.Layers.FFN
import IP.BitNet.Attention.Quantize
import IP.BitNet.Attention.DotProduct
import IP.BitNet.Attention.QKVProjection
import IP.BitNet.Attention.Softmax
import IP.BitNet.Attention.ScoreVMul
import IP.BitNet.Attention.MultiHead
import IP.BitNet.Attention.Top
import IP.BitNet.Spec.FixedPoint
import IP.BitNet.Spec.DotProduct
import IP.BitNet.Proof.ScaleCorrectness
import IP.BitNet.Proof.ReLUSqCorrectness
import IP.BitNet.Proof.ResidualCorrectness
import IP.BitNet.Proof.ElemMulCorrectness
import IP.BitNet.Proof.BitWidthTheorems
import IP.BitNet.Proof.DotProductCorrectness
import IP.BitNet.Proof.AttentionBitWidth
import IP.BitNet.Proof.SoftmaxCorrectness
import IP.BitNet.BitLinear.Dynamic
import IP.BitNet.SoC.Top
