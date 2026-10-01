/-
  Thin `lean_exe` driver for `Sparkle.Tests.ParamSimTest.main`
  (AllTests.lean calls the namespaced `main` directly).
-/
import Tests.ParamSimTest

def main : IO Unit := Sparkle.Tests.ParamSimTest.main
