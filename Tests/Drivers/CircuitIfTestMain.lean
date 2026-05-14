/-
  Thin `lean_exe` driver for `Sparkle.Tests.CircuitIfTest.main`.

  The namespaced `main` lives in `Tests/CircuitIfTest.lean`;
  AllTests.lean imports that file and calls the namespaced
  `main` directly, so we keep this wrapper minimal — just
  enough for `lake exe` to find a top-level `main` symbol.
-/
import Tests.CircuitIfTest

def main : IO Unit := Sparkle.Tests.CircuitIfTest.main
