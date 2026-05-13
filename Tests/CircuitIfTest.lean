/-
  Tests for the statement-level `if cond then … else …`
  extension to `Signal.circuit do`.

  Verifies four things:

    1. A single `if` at the top level desugars to `Signal.mux`
       on the right-hand side, matching what a hand-written
       `cnt <~ Signal.mux cond thenRhs elseRhs` would produce.

    2. Multi-register `if` branches each get their own muxed
       `<~`, so two registers can be reset/incremented together
       without restructuring as separate value-level
       expressions.

    3. Hold semantics: a register assigned in only one branch
       keeps its current value on the other side, matching the
       Verilog `always_ff` non-blocking-assignment convention.

    4. Nested `if c1 then if c2 then … else … else …` collapses
       bottom-up into a single `Signal.mux c1 (Signal.mux c2 …
       …) …`, the natural priority-mux Verilog users expect.

  Each test runs the resulting Signal via the existing
  `Signal.loop` FFI and checks the output sequence cycle-by-
  cycle.  `lake exe circuit-if-test` runs them all and exits
  non-zero on any divergence.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.CircuitIfTest

/-! ### Test 1 — single `if`, single register -/

/-- Counter that resets to 0 when `reset` is high. -/
def resetCounter (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
    else
      cnt <~ cnt + 1#8
    return cnt

/-! ### Test 2 — single `if`, two registers in both branches -/

/-- Two registers stepped together; both reset on `reset`. -/
def twoRegsBoth (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  let bundled := Signal.circuit do
    let cnt ← Signal.reg 0#8
    let acc ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
      acc <~ 0#8
    else
      cnt <~ cnt + 1#8
      acc <~ acc + cnt
    return bundle2 cnt acc
  bundled

/-! ### Test 3 — hold semantics: only one branch assigns

    `acc` is assigned only in the `else` branch.  In the
    `then` branch it should hold its previous value (the
    macro emits `acc <~ Signal.mux reset acc rhs`, where the
    `then`-side `acc` reads the current cycle's value). -/
def heldRegister (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg 0#8
    let acc ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
      -- acc not assigned: should hold current value
    else
      cnt <~ cnt + 1#8
      acc <~ acc + 1#8
    return bundle2 cnt acc

/-! ### Test 4 — nested `if`, priority-mux style -/

/-- Priority-mux: `reset` wins; otherwise `enable` increments,
    otherwise hold.

    Macro lowers this bottom-up: the inner `if enable then …
    else …` collapses to `cnt <~ Signal.mux enable (cnt + 1)
    cnt`; the outer `if reset then 0 else (Signal.mux enable
    …)` then becomes `cnt <~ Signal.mux reset 0 (Signal.mux
    enable (cnt + 1) cnt)`. -/
def priorityMux (reset enable : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let cnt ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
    else
      if enable then
        cnt <~ cnt + 1#8
      else
        cnt <~ cnt
    return cnt

/-! ### Drivers -/

/-- Sample a `Signal defaultDomain α` across the first `n` cycles. -/
def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

/-- A pulse: high at cycles `pulseAt`, low elsewhere. -/
def pulseAt (cycles : List Nat) : Signal defaultDomain Bool :=
  ⟨fun t => cycles.contains t⟩

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
  -- Reset at cycle 3, enable always true otherwise.
  let reset : Signal defaultDomain Bool := pulseAt [3]
  let enable : Signal defaultDomain Bool := Signal.pure true

  let mut ok := true

  -- 1. resetCounter: counts 0,1,2,3, sees reset at cycle 3 →
  -- register *next* value becomes 0, so cycle-4 output is 0,
  -- then 1, 2.  (Reset arrives during cycle 3, register
  -- captures 0 for cycle 4.)
  let r1 := sampleN (resetCounter reset) 8 |>.map toString
  ok := (← runTest "resetCounter" r1 ["0x00#8", "0x01#8", "0x02#8", "0x03#8", "0x00#8", "0x01#8", "0x02#8", "0x03#8"]) && ok

  -- 2. twoRegsBoth: cnt counts up; acc accumulates the *previous*
  -- cnt (because at cycle t, acc <~ acc + cnt uses the
  -- current-cycle cnt = t).  Both reset at cycle 3.
  --   cycle 0: cnt=0 acc=0
  --   cycle 1: cnt=1 acc=0+0=0
  --   cycle 2: cnt=2 acc=0+1=1
  --   cycle 3: cnt=3 acc=1+2=3   (reset here)
  --   cycle 4: cnt=0 acc=0       (reset took effect)
  --   cycle 5: cnt=1 acc=0+0=0
  --   cycle 6: cnt=2 acc=0+1=1
  let r2 := sampleN (twoRegsBoth reset) 7 |>.map (fun p => s!"({p.1},{p.2})")
  ok := (← runTest "twoRegsBoth" r2
          ["(0x00#8,0x00#8)", "(0x01#8,0x00#8)", "(0x02#8,0x01#8)", "(0x03#8,0x03#8)",
           "(0x00#8,0x00#8)", "(0x01#8,0x00#8)", "(0x02#8,0x01#8)"]) && ok

  -- 3. heldRegister: when reset fires, acc holds its previous
  -- value (3 at cycle 3 if it had been accumulating).
  --   cycle 0: cnt=0 acc=0
  --   cycle 1: cnt=1 acc=0+1=1   (else branch, acc gets acc+1)
  --   cycle 2: cnt=2 acc=1+1=2
  --   cycle 3: cnt=3 acc=2+1=3   (reset fires; then-branch holds acc → next cycle acc still 3)
  --   cycle 4: cnt=0 acc=3       (reset took effect on cnt; acc held)
  --   cycle 5: cnt=1 acc=3+1=4
  --   cycle 6: cnt=2 acc=4+1=5
  let r3 := sampleN (heldRegister reset) 7 |>.map (fun p => s!"({p.1},{p.2})")
  ok := (← runTest "heldRegister" r3
          ["(0x00#8,0x00#8)", "(0x01#8,0x01#8)", "(0x02#8,0x02#8)", "(0x03#8,0x03#8)",
           "(0x00#8,0x03#8)", "(0x01#8,0x04#8)", "(0x02#8,0x05#8)"]) && ok

  -- 4. priorityMux: with enable=true except cycle 5, reset at cycle 3.
  --   Same as resetCounter but with the extra enable gate.
  let enable2 : Signal defaultDomain Bool := ⟨fun t => t != 5⟩
  let r4 := sampleN (priorityMux reset enable2) 8 |>.map toString
  ok := (← runTest "priorityMux" r4
          ["0x00#8", "0x01#8", "0x02#8", "0x03#8", "0x00#8", "0x01#8", "0x01#8", "0x02#8"]) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"
end Sparkle.Tests.CircuitIfTest

def main : IO Unit := Sparkle.Tests.CircuitIfTest.main
