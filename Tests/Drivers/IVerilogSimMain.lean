/-
  Thin `lean_exe` driver for `Sparkle.Tests.RoundTrip.IVerilogSim.main`.
-/
import Tests.RoundTrip.IVerilogSim

def main : IO UInt32 := Sparkle.Tests.RoundTrip.IVerilogSim.main
