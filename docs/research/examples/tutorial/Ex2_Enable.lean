-- Tutorial example 2: two extensions of the register, both still proved.
--   (a) a register with an enable input (two inputs, one output);
--   (b) an 8-bit counter that counts only while `en` is high (state fed back).
-- Run from the repository root:
--   lake build Tools.VedU1Entry
--   lake env lean docs/research/examples/tutorial/Ex2_Enable.lean ; echo "exit $?"
import Tools.VedU1Entry
import Sparkle.Core.CircuitMonad

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- (a) Two inputs: `en` (one bit) and `x` (8 bits). Starts at 0; at time t+1 it is
`x` at time t if `en` was high at t, otherwise it keeps its value. -/
def enReg8 (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.registerWithEnable 0#8 en x

#ved_u1 enReg8

/-- info: 'enReg8.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms enReg8.ved_u1

/-- (b) One input `en`, one output, one 8-bit register that starts at 0 and is fed
back: the output is the register, the next value is `r + 1` when `en` is high. -/
def counter8 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  runCircuitH (αs := [BitVec 8]) (0#8, ())
    (fun regs => do
      let (r0, _) := regs
      Circuit.next r0 (Signal.mux en (Circuit.read r0 + 1#8) (Circuit.read r0))
      return Circuit.read r0)

#ved_u1 counter8

/-- info: 'counter8.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counter8.ved_u1
