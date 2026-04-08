/-
  BitNet Top-Level — Signal DSL

  Entry point for the BitNet accelerator.
  All modules are now Signal DSL functions — no CircuitM.

  For Verilog generation, use #synthesizeVerilog on concrete definitions.
  For simulation testing, call Signal functions directly with Signal.pure inputs.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.Config
import IP.BitNet.SignalHelpers
import IP.BitNet.BitLinear.Core
import IP.BitNet.BitLinear.Top
import IP.BitNet.BitLinear.Scale
import IP.BitNet.BitLinear.Dynamic
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
import IP.BitNet.SoC.Top

-- Re-export all BitNet modules for convenient access
open Sparkle.IP.BitNet
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.Attention
open Sparkle.IP.BitNet.SoC
