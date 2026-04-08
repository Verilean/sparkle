/-
  Sparkle HDL - Root Module

  A functional hardware description language in Lean 4.
  Inspired by Haskell's Clash, designed for type-safe hardware design.
-/

import Sparkle.Core.Domain
import Sparkle.Core.Signal
import Sparkle.Core.StateMacro
import Sparkle.Core.Vector
import Sparkle.Core.OptimizedSim
import Sparkle.Data.BitPack
import Sparkle.IR.Type
import Sparkle.IR.AST
import Sparkle.IR.Builder
import Sparkle.IR.Optimize
import Sparkle.Compiler.Elab
import Sparkle.Compiler.DRC
import Sparkle.Backend.Verilog
import Sparkle.Backend.VCD
import Sparkle.Backend.CppSim
import Sparkle.Verification.Temporal
import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Core.SimParallel
import Sparkle.Core.Oracle
import Sparkle.Core.OracleSpec
import Sparkle.Core.MulOracle
import Sparkle.Verification.MulProps
import Sparkle.Utils.HexLoader
