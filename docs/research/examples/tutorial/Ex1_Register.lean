-- Tutorial example 1: an 8-bit register that is proved.
-- Run from the repository root:
--   lake build Tools.VedU1Entry
--   lake env lean docs/research/examples/tutorial/Ex1_Register.lean ; echo "exit $?"
import Tools.VedU1Entry

open Sparkle.Core.Domain Sparkle.Core.Signal

/-- One input `x`, one output, one 8-bit register that starts at 0.
The output at time 0 is the initial value; at time t+1 it is `x` at time t. -/
def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

-- Synthesise delay8 and, in the same command, build and kernel-check the
-- theorem that the returned module computes delay8 (`delay8.ved_u1`).
#ved_u1 delay8

-- The axioms of the theorem are exactly the standard three.
/-- info: 'delay8.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms delay8.ved_u1

-- The waveform of the tutorial (one illustration). The input stream is
-- 5, 9, 9, 3, 7, ... and the output of the SOURCE MEANING is read at t = 0..4.
-- (The theorem covers every stream and every time; this is only a sample.)
def sample : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => [5#8, 9#8, 9#8, 3#8, 7#8].getD t 0#8⟩

#guard (List.range 5).map (fun t => (delay8 sample).val t) == [0#8, 5#8, 9#8, 9#8, 3#8]
