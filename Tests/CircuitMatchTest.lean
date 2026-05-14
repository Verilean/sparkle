/-
  Sim + synth tests for the statement-level `match` extension
  to `Signal.circuit do`.

  The macro extends `circuitStmt` with a Verilog-`case`-style
  pattern-match:

      Signal.circuit do
        let state ← Signal.reg 0#2
        match state with
        | 0#2 => state <~ 1#2
        | 1#2 => state <~ 2#2
        | 2#2 => state <~ 0#2
        | _   => state <~ 0#2
        return state

  The macro lowers this to a right-folded `Signal.mux` chain
  on the equality of `state` against each non-wildcard pattern,
  with the wildcard arm's rhs at the tail.  A register that
  isn't assigned in some arm holds its current value on that
  arm (the same hold semantics the `if/else` extension uses).

  Coverage:

    1. FSM state machine — three explicit states + wildcard,
       cycle-by-cycle output matches the hand-rolled
       Signal.mux chain.
    2. Multiple registers in a single arm.
    3. Hold semantics for a register that's assigned only in
       some arms.
    4. Wildcard mandatory — verified manually (commented out
       to keep `lake build` green).

  Each `def` is also `#synthesizeVerilog`'d so the build catches
  IR-elaborator regressions on the lowered Signal.mux chain.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.CircuitMatchTest

/-! ### 1. Three-state FSM -/

/-- A simple cyclic FSM: 0 → 1 → 2 → 0 → … -/
def fsm3 : Signal defaultDomain (BitVec 2) :=
  Signal.circuit do
    let state ← Signal.reg 0#2
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 => state <~ 2#2
    | 2#2 => state <~ 0#2
    | _   => state <~ 0#2
    return state

/-! ### 2. Multi-register arm -/

/-- FSM that drives a `count` register conditionally on state.
    Demonstrates that `match` can update more than one register
    inside an arm, and the macro emits the right per-register
    mux chain.  Returns just `count` so the synth target is a
    single-Signal output (the existing IR elaborator path for
    `bundle2`-output modules has separate rules we don't need
    to engage here). -/
def fsmWithCount : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let state ← Signal.reg 0#2
    let count ← Signal.reg 0#8
    match state with
    | 0#2 =>
      state <~ 1#2
      count <~ count + 1#8
    | 1#2 =>
      state <~ 2#2
      count <~ count + 1#8
    | _ =>
      state <~ 0#2
      count <~ 0#8
    return count

/-! ### 3. Hold semantics -/

/-- `extra` is assigned only in the `1#2` arm.  In every other
    arm it should hold its previous value, matching what the
    equivalent `if/else` chain would produce.

    Returns just `extra` so the synth target is single-Signal;
    the sim test checks `extra` only (the state ordering is
    already covered by `fsm3`). -/
def fsmHold : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let state ← Signal.reg 0#2
    let extra ← Signal.reg 0#8
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 =>
      state <~ 2#2
      extra <~ extra + 1#8
    | _ => state <~ 0#2
    return extra

end Sparkle.Tests.CircuitMatchTest

section SynthesisChecks
open Sparkle.Tests.CircuitMatchTest

#synthesizeVerilog fsm3
#synthesizeVerilog fsmWithCount
#synthesizeVerilog fsmHold

end SynthesisChecks

namespace Sparkle.Tests.CircuitMatchTest

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def runTest (name : String) (got expected : List String) : IO Bool := do
  IO.println s!"--- {name} ---"
  IO.println s!"  got      = {got}"
  IO.println s!"  expected = {expected}"
  if got = expected then
    IO.println "  PASS"
    return true
  else do
    IO.println "  FAIL"
    return false

def main : IO Unit := do
  let mut ok := true

  -- 1. fsm3: 0,1,2,0,1,2,…
  let r1 := sampleN fsm3 6 |>.map toString
  ok := (← runTest "fsm3" r1 ["0x0#2", "0x1#2", "0x2#2", "0x0#2", "0x1#2", "0x2#2"]) && ok

  -- 2. fsmWithCount: count cycles 0,1,2,0,1,2 alongside state
  -- (state goes through fsm3's pattern).
  let r2 := sampleN fsmWithCount 6 |>.map toString
  ok := (← runTest "fsmWithCount" r2
          ["0x00#8", "0x01#8", "0x02#8", "0x00#8", "0x01#8", "0x02#8"]) && ok

  -- 3. fsmHold: extra only increments when state=1, otherwise holds.
  --   cycle 0: state=0, extra=0 → next state=1, extra holds (0)
  --   cycle 1: state=1, extra=0 → next state=2, extra=1
  --   cycle 2: state=2 (wildcard), extra=1 → next state=0, extra holds (1)
  --   cycle 3: state=0, extra=1 → next state=1, extra holds (1)
  --   cycle 4: state=1, extra=1 → next state=2, extra=2
  --   cycle 5: state=2, extra=2 → next state=0, extra holds (2)
  let r3 := sampleN fsmHold 6 |>.map toString
  ok := (← runTest "fsmHold" r3
          ["0x00#8", "0x00#8", "0x01#8", "0x01#8", "0x01#8", "0x02#8"]) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitMatchTest

def main : IO Unit := Sparkle.Tests.CircuitMatchTest.main
