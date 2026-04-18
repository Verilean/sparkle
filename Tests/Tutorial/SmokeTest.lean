/-
  Tutorial runtime smoke test.

  Actually EXECUTES the Signal DSL counter from `docs/Tutorial.md` Step 1
  — `lake env lean` alone only type-checks, and the C FFI symbols needed
  by `Signal.loop`'s memoization barrier are not available to the Lean
  interpreter. `lean_exe … supportInterpreter := true` links them, so
  `lake exe tutorial-smoke` exercises the real runtime path.

  Asserts the counter produces the expected `[0, 1, …, 9]` sequence.
  (The `+ 1` happens *before* the register: on cycle t the loop sees
  `count = t`, computes `count + 1 = t + 1`, and registers it; sampling
  then reads the registered value which on cycle t is `t`.)
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

def counter8 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  Signal.loop fun count =>
    let next := Signal.mux en (count + 1#8) count
    Signal.register 0#8 next

def main : IO Unit := do
  let values := (counter8 (Signal.pure true)).sample 10
  IO.println s!"Counter: {values}"
  let expected : List (BitVec 8) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  if values = expected then
    IO.println "PASS"
  else do
    IO.println s!"FAIL: expected {expected}"
    IO.Process.exit 1
