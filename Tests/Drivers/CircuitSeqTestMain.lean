/-
  Thin `lean_exe` driver for `Sparkle.Tests.CircuitSeqTest.main`
  (AllTests.lean calls the namespaced `main` directly).
-/
import Tests.CircuitSeqTest

def main : IO Unit := Sparkle.Tests.CircuitSeqTest.main
