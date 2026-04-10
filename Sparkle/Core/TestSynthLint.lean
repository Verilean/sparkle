/-
  Smoke test for `#check_synthesizable`. Interpreter only —
  exercises the command on a few real-world Signal DSL constants.
-/

import Sparkle.Compiler.SynthesizableLint
import IP.BitNet.SoC.Top
import IP.BitNet.SignalHelpers
import IP.BitNet.Layers.FFN
import IP.RV32.BitNetPeripheral

open Sparkle.IP.BitNet.SoC
open Sparkle.IP.BitNet.SignalHelpers
open Sparkle.IP.BitNet.Layers
open Sparkle.IP.RV32.BitNetPeripheral

-- hardwiredSoCSignal — should be clean now (no Id.run, no ite)
#check_synthesizable hardwiredSoCSignal

-- bitNetSoCSignal — still has match on ArchMode (N2 expected)
#check_synthesizable bitNetSoCSignal

-- Level-1a peripheral — calls hardwiredSoCSignal directly, should be clean
#check_synthesizable bitNetPeripheral

-- Lower-level helpers — should be clean after rewrite
-- Note: adderTree is `partial` so has no body; lint it via bitLinearSignal which calls it.
#check_synthesizable bitLinearSignal
#check_synthesizable ffnBlockSignal
