/-
  Tests for `Sparkle.Core.CircuitMonad` (v2 — HList / Prod-chain
  state).

  Two parts:

  1. Simulation parity vs. the existing `Signal.circuit do`
     macro.  Each monadic circuit is paired with its macro
     equivalent and both are sampled cycle-by-cycle through
     the native `Signal.loop` FFI.  Pass = outputs identical.

  2. Synthesis.  Where v1's `Signal dom (Vector τ n)` died on
     `#synthesizeVerilog`, v2's state lives on a Prod chain
     the IR elaborator already lowers.  If this works, the
     macro+monad split becomes a real choice rather than
     "macro for synth, monad for sim only".
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core

namespace Sparkle.Tests.CircuitMonadV2Test

/-! ### 1. Single-register counter -/

/-- Monad version. -/
def counterMonad : Signal defaultDomain (BitVec 8) :=
  runCircuit1 (0#8) (fun count => do
    Circuit.next count (Circuit.read count + 1#8)
    return Circuit.read count)

/-- Macro reference. -/
def counterMacro : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

/-! ### 2. Two-register state (same element type for now —
       heterogeneous test deferred until BitVec.zeroExtend is in
       the elaborator's wire-recognition set). -/

/-- Two coupled counters: `a` counts up, `b` counts down.  Final
    output is their sum, demonstrating that both register slots
    are accessible and assignable through the monadic surface. -/
def twoCountMonad : Signal defaultDomain (BitVec 8) :=
  runCircuit2 (0#8) (0xFF#8) (fun a b => do
    Circuit.next a (Circuit.read a + 1#8)
    Circuit.next b (Circuit.read b - 1#8)
    return Circuit.read a + Circuit.read b)

/-- Macro reference. -/
def twoCountMacro : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let a ← Signal.reg (0#8)
    let b ← Signal.reg (0xFF#8)
    a <~ a + 1#8
    b <~ b - 1#8
    return a + b

/-! ### 3. Heterogeneous-width registers — v2's headline benefit.

    v1's `Vector τ n` state could only hold registers of one
    element type.  v2's Prod-chain state can mix arbitrary
    Wireable types — here a `BitVec 4` count + a `BitVec 8`
    accumulator.  The output is the BitVec-8 accumulator,
    each cycle += a constant ext of the low-4-bit count.

    The "extension" is expressed as `(0#4 ++ count)`, which
    appends a 4-bit zero on the high side — the elaborator
    lowers `Signal ++ BitVec` to wire concat (see
    `Sparkle/Compiler/Elab.lean` line 481-516 for the rule).
    Avoids zeroExtend, which doesn't have a wire-translation
    rule yet. -/

/-- Two registers of *different* widths.  Tests that the v2
    state Prod packs widths additively (4 + 8 = 12-bit packed
    state, each slot wired by its own width). -/
def mixedWidthMonad : Signal defaultDomain (BitVec 8) :=
  runCircuit2 (0#4) (0#8) (fun cnt acc => do
    Circuit.next cnt (Circuit.read cnt + 1#4)
    Circuit.next acc (Circuit.read acc + (0#4 ++ Circuit.read cnt))
    return Circuit.read acc)

/-- Macro reference. -/
def mixedWidthMacro : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg (0#4)
    let acc ← Signal.reg (0#8)
    cnt <~ cnt + 1#4
    acc <~ acc + (0#4 ++ cnt)
    return acc

/-! ### 4. Three registers (arity-3 generalization) -/

/-- Triple counter: a counts up by 1, b by 2, c by 3.  Output
    is `a ^^^ b ^^^ c` (XOR of all three) so each register
    contributes observably.  Exercises `runCircuit3`. -/
def tripleCountMonad : Signal defaultDomain (BitVec 8) :=
  runCircuit3 (0#8) (0#8) (0#8) (fun a b c => do
    Circuit.next a (Circuit.read a + 1#8)
    Circuit.next b (Circuit.read b + 2#8)
    Circuit.next c (Circuit.read c + 3#8)
    return Circuit.read a ^^^ Circuit.read b ^^^ Circuit.read c)

/-- Macro reference. -/
def tripleCountMacro : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let a ← Signal.reg (0#8)
    let b ← Signal.reg (0#8)
    let c ← Signal.reg (0#8)
    a <~ a + 1#8
    b <~ b + 2#8
    c <~ c + 3#8
    return a ^^^ b ^^^ c

end Sparkle.Tests.CircuitMonadV2Test

/-! ### Synthesis smoke checks.

    The whole point of v2: these should compile (where the v1
    PoC died at this exact line). -/
section SynthesisChecks
open Sparkle.Tests.CircuitMonadV2Test

#synthesizeVerilog counterMonad
#synthesizeVerilog counterMacro
#synthesizeVerilog twoCountMonad
#synthesizeVerilog twoCountMacro
#synthesizeVerilog mixedWidthMonad
#synthesizeVerilog mixedWidthMacro
#synthesizeVerilog tripleCountMonad
#synthesizeVerilog tripleCountMacro

end SynthesisChecks

namespace Sparkle.Tests.CircuitMonadV2Test

/-! ### Simulation driver -/

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def runTest (name : String) (got expected : List String) : IO Bool := do
  IO.println s!"--- {name} ---"
  IO.println s!"  got      = {got}"
  IO.println s!"  expected = {expected}"
  if got = expected then
    IO.println "  PASS"
    return true
  else
    IO.println "  FAIL"
    return false

def main : IO Unit := do
  let mut ok := true

  -- 1. counterMonad matches counterMacro on the first 6 cycles.
  let r1m := sampleN counterMonad 6 |>.map toString
  let r1M := sampleN counterMacro 6 |>.map toString
  ok := (← runTest "counterMonad ≡ counterMacro" r1m r1M) && ok

  -- 2. twoCountMonad matches twoCountMacro.
  let r2m := sampleN twoCountMonad 6 |>.map toString
  let r2M := sampleN twoCountMacro 6 |>.map toString
  ok := (← runTest "twoCountMonad ≡ twoCountMacro" r2m r2M) && ok

  -- 3. mixedWidthMonad (BitVec 4 + BitVec 8) matches mixedWidthMacro.
  let r3m := sampleN mixedWidthMonad 8 |>.map toString
  let r3M := sampleN mixedWidthMacro 8 |>.map toString
  ok := (← runTest "mixedWidthMonad ≡ mixedWidthMacro" r3m r3M) && ok

  -- 4. tripleCountMonad (3 registers) matches tripleCountMacro.
  let r4m := sampleN tripleCountMonad 6 |>.map toString
  let r4M := sampleN tripleCountMacro 6 |>.map toString
  ok := (← runTest "tripleCountMonad ≡ tripleCountMacro" r4m r4M) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitMonadV2Test
