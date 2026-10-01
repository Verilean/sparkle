/-
  Thin `lean_exe` driver for `Sparkle.Tests.SystolicTest.main`
  (AllTests.lean calls the namespaced `main` directly).
-/
import Tests.SystolicTest

def main : IO Unit := Sparkle.Tests.SystolicTest.main
