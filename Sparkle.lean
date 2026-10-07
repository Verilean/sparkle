/-
  Sparkle HDL - Root Module

  A functional hardware description language in Lean 4.
  Inspired by Haskell's Clash, designed for type-safe hardware design.
-/

import Sparkle.Core.Domain
import Sparkle.Core.Signal
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Core.SignalLeavesDerive
import Sparkle.Core.StateMacro
import Sparkle.Core.Vector
import Sparkle.Core.OptimizedSim
import Sparkle.Data.BitPack
import Sparkle.IR.Type
import Sparkle.IR.AST
-- The PROVEN IR semantics and the reorder-invariance layer must be in
-- the umbrella: the precompiled Tools.SVParser shared library's object
-- code references their symbols (weWithReads, the decidable checkers),
-- and the dynamic loader can only resolve those from
-- libsparkle_Sparkle.so.  Without these imports a cold `lake build`
-- fails at Sparkle.Verification.CounterProps with
-- "undefined symbol: lp_sparkle_Sparkle_IR_Semantics_weWithReads".
import Sparkle.IR.Semantics
import Sparkle.IR.ReorderInvariance
import Sparkle.IR.Builder
import Sparkle.IR.Optimize
import Sparkle.IR.Specialize
import Sparkle.Compiler.Elab
import Sparkle.Compiler.DRC
import Sparkle.Backend.Verilog
import Sparkle.Backend.VCD
import Sparkle.Backend.CSim
import Sparkle.Verification.Temporal
import Sparkle.Verification.Equivalence
import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Core.Sim
import Sparkle.Core.SimPureLean
import Sparkle.Core.SimVerilator
import Sparkle.Core.SimParallel
import Sparkle.Core.Oracle
import Sparkle.Core.OracleSpec
import Sparkle.Core.MulOracle
import Sparkle.Verification.MulProps
import Sparkle.Utils.HexLoader
import Sparkle.Display
