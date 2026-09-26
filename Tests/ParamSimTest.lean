/-
  Width-parameterized sequential circuits: synthesis with the width kept
  as a Verilog parameter, and JIT simulation of explicit configurations.

    1. `#synthesizeParameterizedVerilog` accepts registers (the module
       keeps `W` as a parameter; the reset literal is size-cast to `W`).
    2. `#sim f [W := n]` specializes the retained design to W = n and
       builds a JIT simulator `f_Wn.Sim`.  Each configuration is checked
       cycle by cycle against the Lean reference `Signal.val` at
       W = 3 (wraps quickly), 17, and 65 (wide input and output ports:
       several 32-bit JIT slots each).
    3. The `circuit do` form and the hand-written `Signal.loop` form of the
       same accumulator agree in simulation.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitDo
import Sparkle.Core.JIT

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.ParamSimTest

/-- Accumulator of width `W`: `acc(t+1) = acc(t) + x(t)`, `acc(0) = 0`. -/
def paramAcc {dom : DomainConfig} {W : Nat}
    (x : Signal dom (BitVec W)) : Signal dom (BitVec W) :=
  circuit do
    let acc ← Signal.reg 0#W
    acc <~ acc + x
    return acc

/-- The same accumulator written with `Signal.loop` + `Signal.register`,
    reset to 1 so the reset literal is not just zero. -/
def paramAccLoop {dom : DomainConfig} {W : Nat}
    (x : Signal dom (BitVec W)) : Signal dom (BitVec W) :=
  Signal.loop fun acc => Signal.register 1#W (acc + x)

#sim paramAcc [W := 3]
#sim paramAcc [W := 17]
#sim paramAcc [W := 65]
#sim paramAccLoop [W := 17]

section SynthesisChecks
#synthesizeParameterizedVerilog paramAcc [W := 8]
#synthesizeParameterizedVerilog paramAccLoop [W := 8]
end SynthesisChecks

/-- Input stimulus: a large, width-independent pattern, truncated to `W`. -/
def stimulus (W : Nat) (t : Nat) : BitVec W :=
  BitVec.ofNat W ((t + 1) * 0x9E3779B97F4A7C15D + t * t)

def reference (W : Nat) (loopForm : Bool) (n : Nat) : List Nat :=
  let x : Signal defaultDomain (BitVec W) := ⟨stimulus W⟩
  let s := if loopForm then paramAccLoop x else paramAcc x
  (List.range n).map fun t => (s.val t).toNat

/-- Run `n` cycles.  `step` drives `x(t)`, evaluates, and ticks; `read`
    then returns the outputs that evaluation computed, i.e. cycle `t`. -/
def jitTrace {Sim I O : Type} [Sparkle.Core.Sim.Sim Sim I O]
    (sim : Sim) (mk : Nat → I) (out : O → Nat) (n : Nat) : IO (List Nat) := do
  Sparkle.Core.Sim.Sim.reset sim
  let mut acc : List Nat := []
  for t in [0:n] do
    Sparkle.Core.Sim.Sim.step sim (mk t)
    acc := acc ++ [out (← Sparkle.Core.Sim.Sim.read sim)]
  Sparkle.Core.Sim.Sim.destroy sim
  return acc

def check (label : String) (got expected : List Nat) : IO Bool := do
  if got == expected then
    IO.println s!"  PASS {label}"
    return true
  IO.println s!"  FAIL {label}\n    got      {got}\n    expected {expected}"
  return false

def main : IO Unit := do
  IO.println "--- Parameterized JIT simulation vs Signal.val ---"
  let n := 24
  let mut ok := true
  let s3 ← paramAcc_W3.Sim.load
  ok := (← check "paramAcc W=3"
    (← jitTrace s3 (fun t => ({ _gen_x := stimulus 3 t } : paramAcc_W3.Sim.SimInput))
      (fun (o : paramAcc_W3.Sim.SimOutput) => o.out.toNat) n)
    (reference 3 false n)) && ok
  let s17 ← paramAcc_W17.Sim.load
  ok := (← check "paramAcc W=17"
    (← jitTrace s17 (fun t => ({ _gen_x := stimulus 17 t } : paramAcc_W17.Sim.SimInput))
      (fun (o : paramAcc_W17.Sim.SimOutput) => o.out.toNat) n)
    (reference 17 false n)) && ok
  let s65 ← paramAcc_W65.Sim.load
  ok := (← check "paramAcc W=65"
    (← jitTrace s65 (fun t => ({ _gen_x := stimulus 65 t } : paramAcc_W65.Sim.SimInput))
      (fun (o : paramAcc_W65.Sim.SimOutput) => o.out.toNat) n)
    (reference 65 false n)) && ok
  let l17 ← paramAccLoop_W17.Sim.load
  ok := (← check "paramAccLoop W=17 (reset value 1)"
    (← jitTrace l17 (fun t => ({ _gen_x := stimulus 17 t } : paramAccLoop_W17.Sim.SimInput))
      (fun (o : paramAccLoop_W17.Sim.SimOutput) => o.out.toNat) n)
    (reference 17 true n)) && ok
  -- The two source forms differ only in the reset value: offset by one.
  ok := (← check "circuit do vs Signal.loop (W=17, offset 1)"
    ((reference 17 true n).map (· % 2 ^ 17))
    ((reference 17 false n).map fun v => (v + 1) % 2 ^ 17)) && ok
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.ParamSimTest
