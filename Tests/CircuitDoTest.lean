/-
  Tests for `circuit do` — the v2-monad-backed alternative to
  `Signal.circuit do`.  Validates both:
    1. Sim parity with the legacy macro form.
    2. Each lowered `runCircuit{N}` synthesises to Verilog.
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.CircuitDoTest

/-! ### 1. Plain counter — sanity check that registers + `<~`
       + `return` form a working basic. -/

def counterCdo : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    cnt <~ cnt + 1#8
    return cnt

def counterMacro : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg 0#8
    cnt <~ cnt + 1#8
    return cnt

/-! ### 2. Reset counter — statement-level `if/else`.

    The marquee feature of `circuit do`: same `if reset then a
    else b` syntax as the macro, lowering to per-register
    `Signal.mux` automatically. -/

def resetCounterCdo (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
    else
      cnt <~ cnt + 1#8
    return cnt

def resetCounterMacro (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg 0#8
    if reset then cnt <~ 0#8
    else cnt <~ cnt + 1#8
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

def twoRegResetMacro (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
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

    The other branch must keep the register's current value
    (cdoStmt's flattener fills in `$nameStx` as the missing rhs). -/

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

def heldRegMacro (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg 0#8
    let acc ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
    else
      cnt <~ cnt + 1#8
      acc <~ acc + 1#8
    return acc

/-! ### 5. `match` — FSM next-state lowering.

    Same Verilog-`case`-style pattern matching as the legacy
    macro, lowering to a right-folded `Signal.mux` chain on
    `scrut === pat` equality.  Scrutinee may be a `Reg` (as in
    user code) or a `Signal` — the `cdoScrut` typeclass-driven
    injection in the macro normalises either to a `Signal`
    before elaborating the patterns. -/

/-- 3-state FSM via `circuit do { match … with … }`. -/
def fsm3Cdo : Signal defaultDomain (BitVec 2) :=
  circuit do
    let state ← Signal.reg 0#2
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 => state <~ 2#2
    | 2#2 => state <~ 0#2
    | _   => state <~ 0#2
    return state

/-- Same FSM via legacy `Signal.circuit do`. -/
def fsm3Macro : Signal defaultDomain (BitVec 2) :=
  Signal.circuit do
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

def fsmHoldMacro : Signal defaultDomain (BitVec 8) :=
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

/-! ### 6. Duplicate `<~` detection.

    Writing `cnt <~ …` twice at the same statement level should
    be a macro error, not silent last-write-wins.  Matches the
    legacy `Signal.circuit do` macro's behaviour.

    Verified via `#guard_msgs`: the second `cnt <~ …` must
    surface the duplicate-write error. -/

/-- error: circuit do: register `cnt` is assigned with `<~` more than once at the same statement level — last write wins (matches Verilog `always_ff` semantics); merge the assignments into a single `<~` to silence this error.
-/
#guard_msgs in
example : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    cnt <~ 0#8
    cnt <~ cnt + 1#8
    return cnt

end Sparkle.Tests.CircuitDoTest

section SynthesisChecks
open Sparkle.Tests.CircuitDoTest

#synthesizeVerilog counterCdo
#synthesizeVerilog counterMacro
#synthesizeVerilog resetCounterCdo
#synthesizeVerilog resetCounterMacro
#synthesizeVerilog twoRegResetCdo
#synthesizeVerilog twoRegResetMacro
#synthesizeVerilog heldRegCdo
#synthesizeVerilog heldRegMacro
#synthesizeVerilog fsm3Cdo
#synthesizeVerilog fsm3Macro
#synthesizeVerilog fsmHoldCdo
#synthesizeVerilog fsmHoldMacro

end SynthesisChecks

namespace Sparkle.Tests.CircuitDoTest

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

  -- 1. counterCdo matches counterMacro.
  let r1c := sampleN counterCdo 6 |>.map toString
  let r1M := sampleN counterMacro 6 |>.map toString
  ok := (← runTest "counterCdo ≡ counterMacro" r1c r1M) && ok

  -- 2. resetCounter — reset at cycle 3.
  let reset : Signal defaultDomain Bool := ⟨fun t => t == 3⟩
  let r2c := sampleN (resetCounterCdo reset) 8 |>.map toString
  let r2M := sampleN (resetCounterMacro reset) 8 |>.map toString
  ok := (← runTest "resetCounterCdo ≡ resetCounterMacro" r2c r2M) && ok

  -- 3. twoRegReset.
  let r3c := sampleN (twoRegResetCdo reset) 8 |>.map toString
  let r3M := sampleN (twoRegResetMacro reset) 8 |>.map toString
  ok := (← runTest "twoRegResetCdo ≡ twoRegResetMacro" r3c r3M) && ok

  -- 4. heldReg.
  let r4c := sampleN (heldRegCdo reset) 8 |>.map toString
  let r4M := sampleN (heldRegMacro reset) 8 |>.map toString
  ok := (← runTest "heldRegCdo ≡ heldRegMacro" r4c r4M) && ok

  -- 5. fsm3 via match.
  let r5c := sampleN fsm3Cdo 6 |>.map toString
  let r5M := sampleN fsm3Macro 6 |>.map toString
  ok := (← runTest "fsm3Cdo ≡ fsm3Macro" r5c r5M) && ok

  -- 6. fsmHold — match with hold semantics.
  let r6c := sampleN fsmHoldCdo 6 |>.map toString
  let r6M := sampleN fsmHoldMacro 6 |>.map toString
  ok := (← runTest "fsmHoldCdo ≡ fsmHoldMacro" r6c r6M) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitDoTest
