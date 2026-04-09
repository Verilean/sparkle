/-
  Smoke test for `#check_synthesizable`. Interpreter only —
  exercises the command on a few real-world Signal DSL constants.
-/

import Sparkle.Compiler.SynthesizableLint
import IP.BitNet.SoC.Top
import IP.RV32.BitNetPeripheral

open Sparkle.IP.BitNet.SoC
open Sparkle.IP.RV32.BitNetPeripheral

-- BitNet's hardwired path uses `Id.run do` + `let mut` — should flag N1.
#check_synthesizable hardwiredSoCSignal

-- `bitNetSoCSignal` matches on `ArchMode` — should flag N2.
#check_synthesizable bitNetSoCSignal

-- Level-1a peripheral is a plain `(a + a) + (a + a)` — should be clean.
#check_synthesizable bitNetPeripheral
