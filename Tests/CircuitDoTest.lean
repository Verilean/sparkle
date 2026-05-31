/-
  Tests for `circuit do` — the v2-monad-backed register DSL.
  Validates:
    1. Cycle-by-cycle simulation against hand-written reference
       outputs.
    2. Each lowered `runCircuit{N}` synthesises to Verilog
       (the `#synthesizeVerilog` invocations error out the
       build if any module no longer synthesises).
    3. Duplicate `<~` detection via `#guard_msgs`.
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.CircuitDoTest

/-! ### 1. Plain counter — `let r ← Signal.reg` + `<~` + `return`. -/

def counterCdo : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    cnt <~ cnt + 1#8
    return cnt

/-! ### 2. Reset counter — statement-level `if/else`.

    `if reset then a else b` over a Signal Bool lowers to per-
    register `Signal.mux`.  A register assigned in only one
    branch holds its current value on the other side. -/

def resetCounterCdo (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
    else
      cnt <~ cnt + 1#8
    return cnt

/-! ### 3. Two-register if/else, both branches assign both regs. -/

def twoRegResetCdo (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    if reset then
      a <~ 0#8
      b <~ 0#8
    else
      a <~ a + 1#8
      b <~ b + 2#8
    return a + b

/-! ### 4. Hold semantics — register assigned in only one branch.

    `acc` only gets a `<~` in the else branch; on the then
    branch it must keep its current value. -/

def heldRegCdo (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    let acc ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
      -- acc holds
    else
      cnt <~ cnt + 1#8
      acc <~ acc + 1#8
    return acc

/-! ### 5. `match` — FSM next-state lowering.

    Verilog-`case`-style pattern matching, lowered to a right-
    folded `Signal.mux` chain on `scrut === pat` equality. -/

def fsm3Cdo : Signal defaultDomain (BitVec 2) :=
  circuit do
    let state ← Signal.reg 0#2
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 => state <~ 2#2
    | 2#2 => state <~ 0#2
    | _   => state <~ 0#2
    return state

/-- Match with hold semantics: `extra` only updates on state=1. -/
def fsmHoldCdo : Signal defaultDomain (BitVec 8) :=
  circuit do
    let state ← Signal.reg 0#2
    let extra ← Signal.reg 0#8
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 =>
      state <~ 2#2
      extra <~ extra + 1#8
    | _ => state <~ 0#2
    return extra

/-! ### 7. Four-register `circuit do` — exercises the
       `runCircuit4` arity extension. -/

def fourCounterCdo : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    let c ← Signal.reg 0#8
    let d ← Signal.reg 0#8
    a <~ a + 1#8
    b <~ b + 2#8
    c <~ c + 3#8
    d <~ d + 4#8
    return a + b + c + d

end Sparkle.Tests.CircuitDoTest

section SynthesisChecks
open Sparkle.Tests.CircuitDoTest

#synthesizeVerilog counterCdo
#synthesizeVerilog resetCounterCdo
#synthesizeVerilog twoRegResetCdo
#synthesizeVerilog heldRegCdo
#synthesizeVerilog fsm3Cdo
#synthesizeVerilog fsmHoldCdo
#synthesizeVerilog fourCounterCdo

end SynthesisChecks

namespace Sparkle.Tests.CircuitDoTest

/-! ### 6. Duplicate `<~` detection.

    Writing `cnt <~ …` twice at the same statement level is a
    macro error.  Verified via `#guard_msgs`. -/

/-- error: circuit do: register `cnt` is assigned with `<~` more than once at the same statement level — last write wins (matches Verilog `always_ff` semantics); merge the assignments into a single `<~` to silence this error.
-/
#guard_msgs in
example : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    cnt <~ 0#8
    cnt <~ cnt + 1#8
    return cnt

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

  -- 1. counterCdo: 0, 1, 2, 3, 4, 5.
  let r1 := sampleN counterCdo 6 |>.map toString
  ok := (← runTest "counterCdo"
          r1 ["0x00#8", "0x01#8", "0x02#8", "0x03#8", "0x04#8", "0x05#8"]) && ok

  -- 2. resetCounterCdo with reset at cycle 3.
  let reset : Signal defaultDomain Bool := ⟨fun t => t == 3⟩
  let r2 := sampleN (resetCounterCdo reset) 8 |>.map toString
  ok := (← runTest "resetCounterCdo"
          r2 ["0x00#8", "0x01#8", "0x02#8", "0x03#8",
              "0x00#8", "0x01#8", "0x02#8", "0x03#8"]) && ok

  -- 3. twoRegResetCdo with reset at cycle 3.
  --   a counts 0,1,2,3 then resets; b counts 0,2,4,6 then resets.
  --   Sum at each cycle: 0, 3, 6, 9, 0, 3, 6, 9.
  let r3 := sampleN (twoRegResetCdo reset) 8 |>.map toString
  ok := (← runTest "twoRegResetCdo"
          r3 ["0x00#8", "0x03#8", "0x06#8", "0x09#8",
              "0x00#8", "0x03#8", "0x06#8", "0x09#8"]) && ok

  -- 4. heldRegCdo: acc holds on reset, increments on else.
  --   cycle 0-2: cnt counts up, acc = 1,2,3
  --   cycle 3: reset, cnt=0 next cycle, acc holds (=3)
  --   cycle 4-7: cnt counts up again, acc = 3,4,5,6 ...
  let r4 := sampleN (heldRegCdo reset) 8 |>.map toString
  ok := (← runTest "heldRegCdo"
          r4 ["0x00#8", "0x01#8", "0x02#8", "0x03#8",
              "0x03#8", "0x04#8", "0x05#8", "0x06#8"]) && ok

  -- 5. fsm3Cdo: 0 → 1 → 2 → 0 → ...
  let r5 := sampleN fsm3Cdo 6 |>.map toString
  ok := (← runTest "fsm3Cdo"
          r5 ["0x0#2", "0x1#2", "0x2#2", "0x0#2", "0x1#2", "0x2#2"]) && ok

  -- 6. fsmHoldCdo: extra increments only on state=1.
  --   cycle 0: state=0, extra=0 (then state=1, extra holds)
  --   cycle 1: state=1, extra=0 (then state=2, extra=1)
  --   cycle 2: state=2, extra=1 (then state=0, extra holds)
  --   cycle 3: state=0, extra=1 ...
  let r6 := sampleN fsmHoldCdo 6 |>.map toString
  ok := (← runTest "fsmHoldCdo"
          r6 ["0x00#8", "0x00#8", "0x01#8", "0x01#8", "0x01#8", "0x02#8"]) && ok

  -- 7. fourCounterCdo: a/b/c/d count by 1/2/3/4.
  --   cycle k: sum = k*(1+2+3+4) = 10*k
  let r7 := sampleN fourCounterCdo 5 |>.map toString
  ok := (← runTest "fourCounterCdo"
          r7 ["0x00#8", "0x0a#8", "0x14#8", "0x1e#8", "0x28#8"]) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitDoTest
