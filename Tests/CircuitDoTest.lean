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

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitDoTest
