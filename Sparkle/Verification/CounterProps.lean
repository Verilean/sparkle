/-
  Formal Verification of Auto-Generated Verilog Counter

  This file proves properties about the **auto-generated** state machine
  from `Sparkle/Verification/Generated/Counter8.lean`, which is produced
  by parsing this Verilog via SVParser:

    module counter8_en (
        input clk, input rst, input en,
        output [7:0] count
    );
        reg [7:0] count_reg;
        assign count = count_reg;
        always @(posedge clk) begin
            if (rst)      count_reg <= 0;
            else if (en)  count_reg <= count_reg + 1;
        end
    endmodule

  Pipeline: Verilog → [SVParser] → IR → [Verify.lean] → Generated/Counter8.lean → [this file] → Q.E.D.

  No hand-written State/Input/nextState — everything comes from the generated import.
-/

import Sparkle.Verification.Generated.Counter8

open counter8_en.Verify

namespace Sparkle.Verification.CounterProps

-- ============================================================================
-- Formal Properties of the Auto-Generated Counter
-- ============================================================================

/-- Property 1: Counter holds its value when enable is deasserted and not in reset.
    Proves: the auto-generated nextState preserves count when rst=0, en=0. -/
theorem counter_holds_when_disabled (s : State) :
    nextState s { rst := 0, en := 0 } = s := by
  simp [nextState]

/-- Property 2: Reset always clears the counter to zero.
    Proves: the auto-generated nextState sets count_reg=0 when rst=1. -/
theorem counter_resets_to_zero (s : State) (i : Input) :
    i.rst = 1 → (nextState s i).count_reg = 0#8 := by
  intro h; simp [nextState, h]

/-- Property 3: Counter increments by 1 when enabled and not in reset.
    Proves: the auto-generated nextState computes count+1 when rst=0, en=1. -/
theorem counter_increments (s : State) :
    (nextState s { rst := 0, en := 1 }).count_reg = s.count_reg + 1 := by
  simp [nextState]

/-- Property 4: Counter wraps around from 255 to 0 (BitVec 8 overflow).
    Proves: hardware bit-width semantics in the auto-generated model. -/
theorem counter_wraps :
    nextState { count_reg := 255#8 } { rst := 0, en := 1 }
    = { count_reg := 0#8 } := by
  native_decide

-- ============================================================================
-- Multi-step properties
-- ============================================================================

/-- Apply n steps of the counter with constant input -/
def nSteps (s : State) (i : Input) : Nat → State
  | 0 => s
  | n + 1 => nextState (nSteps s i n) i

/-- Property 5: After n enabled steps from 0, counter = n mod 256. -/
theorem counter_counts_correctly (n : Nat) (h : n < 256) :
    (nSteps { count_reg := 0#8 } { rst := 0, en := 1 } n).count_reg
    = BitVec.ofNat 8 n := by
  induction n with
  | zero => simp [nSteps]
  | succ k ih =>
    have hk : k < 256 := Nat.lt_of_succ_lt h
    simp only [nSteps, nextState]; rw [ih hk]; simp
    bv_omega

/-- Property 6: Reset from any state always reaches zero. -/
theorem reset_reaches_zero (s : State) :
    (nSteps s { rst := 1, en := 0 } 1).count_reg = 0#8 := by
  simp [nSteps, nextState]

end Sparkle.Verification.CounterProps
