/-
  BitNet Top-Level — Signal DSL

  Entry point for the BitNet accelerator.
  All modules are now Signal DSL functions — no CircuitM.

  For Verilog generation, use #synthesizeVerilog on concrete definitions.
  For simulation testing, call Signal functions directly with Signal.pure inputs.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Top
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.BitLinear.Dynamic
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
import Examples.BitNet.SoC.Top

-- Re-export all BitNet modules for convenient access
open Sparkle.Examples.BitNet
open Sparkle.Examples.BitNet.Layers
open Sparkle.Examples.BitNet.BitLinear
open Sparkle.Examples.BitNet.Attention
open Sparkle.Examples.BitNet.SoC
