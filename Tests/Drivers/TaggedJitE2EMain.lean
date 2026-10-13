import LSpec
import Tests.Compiler.TaggedJitE2ETest

open LSpec

/-- The tagged-instance JIT end-to-end rows alone (the same rows are part of `Tests.AllTests`). -/
def main : IO UInt32 := do
  let t ← Tests.Compiler.TaggedJitE2ETest.tests
  lspecIO (Std.HashMap.ofList [("tagged-jit-e2e", [t])]) []
