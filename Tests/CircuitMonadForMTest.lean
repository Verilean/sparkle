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

/-! ### Four-stage shift register via `forM`.

    `runCircuit4` provides four BitVec 8 slots; `forM` over a
    list of adjacent pairs `[(r1, r0), (r2, r1), (r3, r2)]`
    schedules each `r_i+1 <~ Circuit.read r_i`.  Output is the
    last stage; an input arriving at cycle k reaches it at
    cycle k+4. -/

def shift4ForM (input : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  runCircuit4 0#8 0#8 0#8 0#8 (fun r0 r1 r2 r3 => do
    Circuit.next r0 input
    [(r1, r0), (r2, r1), (r3, r2)].forM (fun (dst, src) =>
      Circuit.next dst (Circuit.read src))
    return Circuit.read r3)

end Sparkle.Tests.CircuitMonadForMTest

section SynthesisChecks
open Sparkle.Tests.CircuitMonadForMTest

#synthesizeVerilog threeCountersForM
#synthesizeVerilog shift4ForM

end SynthesisChecks

namespace Sparkle.Tests.CircuitMonadForMTest

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def main : IO Unit := do
  let mut ok := true

  -- threeCountersForM samples:
  --   cycle 0: r0=0, r1=1, r2=2 → sum = 3
  --   cycle 1: r0=1, r1=2, r2=3 → sum = 6
  --   ...
  let r1 := sampleN threeCountersForM 6 |>.map toString
  let r1Expected := ["0x03#8", "0x06#8", "0x09#8", "0x0c#8", "0x0f#8", "0x12#8"]
  IO.println s!"--- threeCountersForM ---"
  IO.println s!"  got      = {r1}"
  IO.println s!"  expected = {r1Expected}"
  if r1 == r1Expected then
    IO.println "  PASS"
  else
    IO.println "  FAIL"
    ok := false

  -- shift4ForM: input is cycle index (0,1,2,3,...).  Last stage
  -- shows input from 4 cycles ago, so we get 0,0,0,0,0,1,2,3 for
  -- the first 8 cycles.
  let input : Signal defaultDomain (BitVec 8) :=
    ⟨fun t => (t.toUInt8.toBitVec)⟩
  let r2 := sampleN (shift4ForM input) 8 |>.map toString
  let r2Expected := ["0x00#8", "0x00#8", "0x00#8", "0x00#8",
                     "0x00#8", "0x01#8", "0x02#8", "0x03#8"]
  IO.println s!"--- shift4ForM ---"
  IO.println s!"  got      = {r2}"
  IO.println s!"  expected = {r2Expected}"
  if r2 == r2Expected then
    IO.println "  PASS"
  else
    IO.println "  FAIL"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitMonadForMTest
