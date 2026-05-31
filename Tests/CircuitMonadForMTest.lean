/-
  Demonstrates that the v2 `Circuit` monad supports Lean's
  standard `forM` directly — something the legacy `Signal.circuit
  do` macro couldn't express because it was a syntax-level macro
  that didn't pass through the standard do-notation pipeline.

  This isn't possible with `circuit do` (the macro intercepts
  the `do` keyword), so we go straight to `runCircuit{N}` and
  use Lean's native `do`-block with `Circuit` as the monad.
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core

namespace Sparkle.Tests.CircuitMonadForMTest

/-! ### Three counters incremented via `forM`.

    Three registers, each gets `r <~ r + 1` applied to it via
    `List.forM` on `[r0, r1, r2]`.  Same circuit as if we'd
    written three `Circuit.next` lines by hand, but proves the
    Monad instance composes with Lean's `ForM` typeclass. -/

def threeCountersForM : Signal defaultDomain (BitVec 8) :=
  runCircuit3 0#8 1#8 2#8 (fun r0 r1 r2 => do
    -- Increment each of the three registers using `forM`.
    -- `[r0, r1, r2]` is a `List (Reg dom S (BitVec 8))`.
    -- The lambda runs inside the `Circuit` monad, calling
    -- `Circuit.next` for each register.
    [r0, r1, r2].forM (fun r =>
      Circuit.next r (Circuit.read r + 1#8))
    return Circuit.read r0 + Circuit.read r1 + Circuit.read r2)

end Sparkle.Tests.CircuitMonadForMTest

section SynthesisChecks
open Sparkle.Tests.CircuitMonadForMTest

#synthesizeVerilog threeCountersForM

end SynthesisChecks

namespace Sparkle.Tests.CircuitMonadForMTest

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def main : IO Unit := do
  -- threeCountersForM samples:
  --   cycle 0: r0=0, r1=1, r2=2 → sum = 3
  --   cycle 1: r0=1, r1=2, r2=3 → sum = 6
  --   cycle 2: r0=2, r1=3, r2=4 → sum = 9
  --   ...
  let r := sampleN threeCountersForM 6 |>.map toString
  let expected := ["0x03#8", "0x06#8", "0x09#8", "0x0c#8", "0x0f#8", "0x12#8"]
  IO.println s!"--- threeCountersForM ---"
  IO.println s!"  got      = {r}"
  IO.println s!"  expected = {expected}"
  if r == expected then
    IO.println "  PASS"
  else
    IO.println "  FAIL"
    IO.Process.exit 1

end Sparkle.Tests.CircuitMonadForMTest
