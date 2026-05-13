/-
  Runtime smoke test for `Sparkle.Core.CircuitMonad`.

  `lake env lean` alone only type-checks; the C FFI symbols
  that `Signal.loop`'s memoisation barrier needs are not
  available to the bare Lean interpreter.  Wrapping this file
  as a `lean_exe … supportInterpreter := true` (`lake exe
  circuit-monad-smoke` per the lakefile) links the native side
  and lets us actually evaluate the counter.

  Compares the PoC monad counter against the existing
  `Signal.circuit do` macro counter on the first 10 cycles.
  Both should produce `[0, 1, 2, …, 9]`; the assertion fails
  the process with a non-zero exit code if they diverge,
  so CI catches regressions in either path.
-/

import Sparkle
import Sparkle.Core.CircuitMonad

open Sparkle.Core
open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- 8-bit counter through the ST-style monad PoC.

    With the new index-keyed allocator: the caller provides a
    `Vector` of initial values whose length is the register
    count, and the body receives an allocator `Fin n → Reg`
    keyed on slot index.  The macro expansion (when we wire
    it in) will count `Signal.reg` lines at compile time and
    generate the `Vector.mk` + indexed `handles _` calls. -/
def counterMonad : Signal defaultDomain (BitVec 8) :=
  runCircuit (initVec := #v[0#8]) fun _σ handles => do
    let c := handles 0
    Circuit.next c (Circuit.read c + 1#8)
    pure (Circuit.read c)

/-- 8-bit counter through the existing macro-based DSL.  Same
    behaviour, different surface — used here as a reference
    oracle. -/
def counterMacroRef : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

def main : IO Unit := do
  let monadVals  := counterMonad.sample 10
  let macroVals  := counterMacroRef.sample 10
  let expected : List (BitVec 8) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  IO.println s!"monad : {monadVals}"
  IO.println s!"macro : {macroVals}"
  IO.println s!"want  : {expected}"
  let pass := monadVals = expected && macroVals = expected && monadVals = macroVals
  if pass then
    IO.println "PASS"
  else do
    IO.println "FAIL"
    IO.Process.exit 1
