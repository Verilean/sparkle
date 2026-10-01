/-
  Thin `lean_exe` driver for `Sparkle.Tests.TlmTest.main`
  (AllTests.lean calls the namespaced `main` directly).
-/
import Tests.TlmTest

def main : IO Unit := Sparkle.Tests.TlmTest.main
