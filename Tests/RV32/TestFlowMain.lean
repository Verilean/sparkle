/- Standalone entry point for RV32 flow tests -/
import Tests.RV32.TestFlow
import LSpec

open LSpec

def main : IO UInt32 := do
  let tests ← Sparkle.Tests.RV32.TestFlow.flowTests
  lspecIO (Std.HashMap.ofList [("rv32-flow", [tests])]) []
