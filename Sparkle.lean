/-
  Sparkle HDL - Root Module

  A functional hardware description language in Lean 4.
  Inspired by Haskell's Clash, designed for type-safe hardware design.
-/

import Sparkle.Core.Domain
import Sparkle.Core.Signal
import Sparkle.Core.Vector
import Sparkle.Core.OptimizedSim
import Sparkle.Data.BitPack
import Sparkle.IR.Type
import Sparkle.IR.AST
import Sparkle.IR.Builder
import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog
import Sparkle.Backend.VCD
import Sparkle.Verification.Temporal
