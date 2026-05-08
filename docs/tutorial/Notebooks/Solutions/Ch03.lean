import Sparkle

/-!
# Chapter 3 — reference solutions
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Solutions.Ch03

/-- One-hot encoding of the three lights. -/
def GREEN  : BitVec 3 := 4#3   -- 100
def YELLOW : BitVec 3 := 2#3   -- 010
def RED    : BitVec 3 := 1#3   -- 001

/-- State encoding (matches the order green → yellow → red). -/
def S_GREEN  : BitVec 2 := 0#2
def S_YELLOW : BitVec 2 := 1#2
def S_RED    : BitVec 2 := 2#2

/-- Solution to Ch03 §3.7 — a traffic-light controller.

    The FSM cycles green (8) → yellow (2) → red (6) → green …
    The output is a 3-bit one-hot encoding of the active light. -/
def trafficLight {dom : DomainConfig} : Signal dom (BitVec 3) :=
  Signal.circuit do
    let state ← Signal.reg S_GREEN;
    let timer ← Signal.reg 0#4;
    let isGreen  := state === S_GREEN;
    let isYellow := state === S_YELLOW;
    let isRed    := state === S_RED;
    -- Dwell-time table.  The innermost `Signal.mux` has both
    -- branches as bare BitVec literals — Lean can't infer the
    -- Signal type from the arguments alone, so we lift the
    -- `else` branch with `Signal.lit dom`.
    let limit :=
      Signal.mux isGreen 7#4
        (Signal.mux isYellow 1#4 (Signal.lit dom 5#4));
    let timerExpired := timer === limit;
    -- Next state: advance on expiry, else stay.
    let nextState :=
      Signal.mux (isGreen  &&& timerExpired) S_YELLOW
        (Signal.mux (isYellow &&& timerExpired) S_RED
          (Signal.mux (isRed   &&& timerExpired) S_GREEN state));
    state <~ nextState;
    -- Timer: reset to 0 on a transition, else +1.
    timer <~ Signal.mux timerExpired 0#4 (timer + 1#4);
    -- Output: one-hot of the current state.  Same situation as
    -- the dwell-time table — innermost branch needs a lift.
    let lights :=
      Signal.mux isGreen GREEN
        (Signal.mux isYellow YELLOW (Signal.lit dom RED));
    return lights

end Notebooks.Solutions.Ch03
