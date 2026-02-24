/-
  Sparkle Examples — BitNet b1.58 Verified RTL Generator

  A ROM-fixed BitNet (ternary-weight) LLM inference core in synthesizable RTL,
  generated from Lean 4 via Sparkle HDL. Targets ASIC synthesis for BitNet b1.58 1B.
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Examples.BitNet.MemoryMap
import Examples.BitNet.Primitives.Rom
import Examples.BitNet.BitLinear.BitWidth
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Top
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Layers.ReLUSq
import Examples.BitNet.Layers.ResidualAdd
import Examples.BitNet.Layers.ElemMul
import Examples.BitNet.Layers.RMSNorm
import Examples.BitNet.Layers.FFN
import Examples.BitNet.Attention.Quantize
import Examples.BitNet.Attention.DotProduct
import Examples.BitNet.Attention.QKVProjection
import Examples.BitNet.Attention.Softmax
import Examples.BitNet.Attention.ScoreVMul
import Examples.BitNet.Attention.MultiHead
import Examples.BitNet.Attention.Top
import Examples.BitNet.Spec.FixedPoint
import Examples.BitNet.Spec.DotProduct
import Examples.BitNet.Proof.ScaleCorrectness
import Examples.BitNet.Proof.ReLUSqCorrectness
import Examples.BitNet.Proof.ResidualCorrectness
import Examples.BitNet.Proof.ElemMulCorrectness
import Examples.BitNet.Proof.BitWidthTheorems
import Examples.BitNet.Proof.DotProductCorrectness
import Examples.BitNet.Proof.AttentionBitWidth
import Examples.BitNet.Proof.SoftmaxCorrectness
import Examples.BitNet.BitLinear.Dynamic
import Examples.BitNet.SoC.Top
