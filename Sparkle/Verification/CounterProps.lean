/-
  Inline Verilog Formal Verification

  The `verilog!` macro below parses the Verilog at compile time,
  generating State/Input/nextState definitions. The theorems prove
  properties directly against the auto-generated code.

  Change the Verilog (e.g., `count_reg + 1` → `count_reg + 2`)
  and the proofs below will instantly fail — no simulation needed.
-/

import Tools.SVParser.Macro

-- ============================================================================
-- Verilog source → compiled into Lean definitions at elaboration time
-- ============================================================================

verilog! "
module counter8_en (
    input clk,
    input rst,
    input en,
    output [7:0] count
);
    reg [7:0] count_reg;
    assign count = count_reg;
    always @(posedge clk) begin
        if (rst)
            count_reg <= 0;
        else if (en)
            count_reg <= count_reg + 1;

        // Verilog assertion: reset implies counter is zero
        // This theorem is AUTO-GENERATED and AUTO-PROVED by bv_decide!
        assert(rst ? (count_reg == 0) : 1);
    end
endmodule
"

-- ============================================================================
-- Formal proofs against the auto-generated definitions
-- ============================================================================

open counter8_en.Verify

namespace Sparkle.Verification.CounterProps

/-- Counter holds its value when enable=0 and reset=0. -/
theorem counter_holds_when_disabled (s : State) :
    nextState s { rst := 0, en := 0 } = s := by
  simp [nextState]

/-- Reset always clears the counter to zero. -/
theorem counter_resets_to_zero (s : State) (i : Input) :
    i.rst = 1 → (nextState s i).count_reg = 0#8 := by
  intro h; simp [nextState, h]

/-- Counter increments by 1 when enabled. -/
theorem counter_increments (s : State) :
    (nextState s { rst := 0, en := 1 }).count_reg = s.count_reg + 1 := by
  simp [nextState]

/-- 255 + 1 = 0 in 8-bit hardware (BitVec wrap-around). -/
theorem counter_wraps :
    nextState { count_reg := 255#8 } { rst := 0, en := 1 }
    = { count_reg := 0#8 } := by
  native_decide

/-- Apply n steps with constant input. -/
def nSteps (s : State) (i : Input) : Nat → State
  | 0 => s
  | n + 1 => nextState (nSteps s i n) i

/-- After n enabled steps from 0, counter equals n mod 256. -/
theorem counter_counts_correctly (n : Nat) (h : n < 256) :
    (nSteps { count_reg := 0#8 } { rst := 0, en := 1 } n).count_reg
    = BitVec.ofNat 8 n := by
  induction n with
  | zero => simp [nSteps]
  | succ k ih =>
    have hk : k < 256 := Nat.lt_of_succ_lt h
    simp only [nSteps, nextState]; rw [ih hk]; simp
    bv_omega

/-- Reset from any state reaches zero in 1 cycle. -/
theorem reset_reaches_zero (s : State) :
    (nSteps s { rst := 1, en := 0 } 1).count_reg = 0#8 := by
  simp [nSteps, nextState]

end Sparkle.Verification.CounterProps
