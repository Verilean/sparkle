import Sparkle.IR.Builder
import IP.BitNet.Config

namespace Sparkle.IP.BitNet.Primitives

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type

def mkWeightROM (cfg : BitLinearConfig) : Module :=
  let name := s!"WeightROM_{cfg.outDim}x{cfg.inDim}"
  mkROMPrimitive name cfg.romAddrBits romWordBits

def mkScaleROM (cfg : BitLinearConfig) : Module :=
  let name := s!"ScaleROM_{cfg.outDim}"
  mkROMPrimitive name cfg.scaleAddrBits scaleTotalBits

end Sparkle.IP.BitNet.Primitives
