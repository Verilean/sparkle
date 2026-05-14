/-
  Thin `lean_exe` driver for `Sparkle.Tests.CircuitMatchTest.main`.

  The namespaced `main` lives in `Tests/CircuitMatchTest.lean`;
  AllTests.lean imports that file and calls the namespaced
  `main` directly, so we keep this wrapper minimal — just
  enough for `lake exe` to find a top-level `main` symbol.
-/
import Tests.CircuitMatchTest

def main : IO Unit := Sparkle.Tests.CircuitMatchTest.main
