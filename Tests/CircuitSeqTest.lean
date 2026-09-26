/-
  Tests for `circuit seq do` — multi-cycle sequential programs.

    1. Cycle-by-cycle simulation against hand-derived reference traces
       (waitUntil, single-step `while`, multi-state `while` body, `pause`,
       sequence-level `if`, `halt`, restart after the last statement).
    2. Cross-check: the same algorithm written by hand as a `circuit do`
       FSM (`match` on an explicit state register) gives the same trace.
    3. `#synthesizeVerilog` for every circuit.
    4. Macro errors via `#guard_msgs`.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.CircuitSeqTest

/-! ### 1. Sum four consecutive inputs after `start`. -/

/-- Wait for `start`, clear, add `x` on four consecutive cycles, then
    publish the sum in `result`. -/
def sum4Seq (start : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit seq do
    let acc ← Signal.reg 0#8
    let i ← Signal.reg 0#3
    let result ← Signal.reg 0#8
    waitUntil start
    step
      acc <~ 0#8
      i <~ 0#3
    while Signal.ult i (Signal.pure 4#3) do
      step
        acc <~ acc + x
        i <~ i + 1#3
    step
      result <~ acc
    return result

/-- The same algorithm as a hand-written FSM: 0 wait, 1 clear, 2 loop,
    3 publish. -/
def sum4Fsm (start : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let i ← Signal.reg 0#3
    let result ← Signal.reg 0#8
    let st ← Signal.reg 0#2
    match st with
    | 0#2 =>
      if start then
        st <~ 1#2
      else
    | 1#2 =>
      acc <~ 0#8
      i <~ 0#3
      st <~ 2#2
    | 2#2 =>
      if Signal.ult i (Signal.pure 4#3) then
        acc <~ acc + x
        i <~ i + 1#3
      else
        st <~ 3#2
    | _ =>
      result <~ acc
      st <~ 0#2
    return result

/-! ### 2. Multi-state loop body, `pause`, sequence-level `if`, `halt`. -/

def nestedSeq : Signal defaultDomain (BitVec 4) :=
  circuit seq do
    let n ← Signal.reg 0#4
    let k ← Signal.reg 0#2
    while Signal.ult k (Signal.pure 2#2) do
      step
        n <~ n + 1#4
      pause
      step
        k <~ k + 1#2
    if Signal.ult n (Signal.pure 3#4) then
      step
        n <~ 10#4
    else
      step
        n <~ 0#4
    halt
    return n

/-! ### 3. A program that restarts: a two-state toggle. -/

def toggleSeq : Signal defaultDomain (BitVec 1) :=
  circuit seq do
    let b ← Signal.reg 0#1
    step
      b <~ 1#1
    step
      b <~ 0#1
    return b

section SynthesisChecks
#synthesizeVerilog sum4Seq
#synthesizeVerilog sum4Fsm
#synthesizeVerilog nestedSeq
#synthesizeVerilog toggleSeq
end SynthesisChecks

/-! ### 4. Macro errors. -/

/-- error: circuit seq do: the program is empty (add a `step`, `waitUntil`, …) -/
#guard_msgs in
example : Signal defaultDomain (BitVec 1) :=
  circuit seq do
    let b ← Signal.reg 0#1
    return b

/-- error: circuit seq do: put `<~`, `if` and `match` inside a `step` -/
#guard_msgs in
example : Signal defaultDomain (BitVec 1) :=
  circuit seq do
    let b ← Signal.reg 0#1
    b <~ 1#1
    return b

/-! ### Simulation driver. -/

def sampleN {α} (s : Signal defaultDomain α) (n : Nat) : List α :=
  (List.range n).map (fun i => s.val i)

def check (label : String) (got expected : List Nat) : IO Bool := do
  if got == expected then
    IO.println s!"  PASS {label}"
    return true
  IO.println s!"  FAIL {label}\n    got      {got}\n    expected {expected}"
  return false

def main : IO Unit := do
  IO.println "--- circuit seq do ---"
  let mut ok := true
  -- start pulses at cycle 2; x(t) = t.  Clear at t3, loop t4..t7 adds
  -- 4+5+6+7 = 22, exit test t8, publish t9 (visible t10), then wait again.
  let start : Signal defaultDomain Bool := ⟨fun t => t == 2⟩
  let x : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 t⟩
  let sumExpected := List.replicate 10 0 ++ List.replicate 4 22
  let sumGot := (sampleN (sum4Seq start x) 14).map (·.toNat)
  ok := (← check "sum4Seq trace" sumGot sumExpected) && ok
  -- A second start pulse after the program restarts: sums x at t14..t17.
  let start2 : Signal defaultDomain Bool := ⟨fun t => t == 2 || t == 12⟩
  let seqLong := (sampleN (sum4Seq start2 x) 24).map (·.toNat)
  let fsmLong := (sampleN (sum4Fsm start2 x) 24).map (·.toNat)
  ok := (← check "sum4Seq restarts (second start)" (seqLong.drop 20)
    (List.replicate 4 (14 + 15 + 16 + 17))) && ok
  ok := (← check "sum4Seq == hand-written FSM (24 cycles)" seqLong fsmLong) && ok
  -- while header t0/t4/t8, n+1 at t1/t5, pause t2/t6, k+1 at t3/t7;
  -- if-test at t9 (n = 2 < 3), n <~ 10 at t10, then halt.
  let nestedExpected := [0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 10, 10, 10, 10, 10]
  ok := (← check "nestedSeq trace" ((sampleN nestedSeq 16).map (·.toNat)) nestedExpected) && ok
  ok := (← check "toggleSeq restarts"
    ((sampleN toggleSeq 6).map (·.toNat)) [0, 1, 0, 1, 0, 1]) && ok
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.CircuitSeqTest
