/-
  Verilog Counter Formal Verification

  Pure state-machine model of an 8-bit counter with enable,
  matching the Sparkle IR output from parsing this Verilog:

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

  The IR produces: register count_reg <= mux(rst, 0, mux(en, count_reg+1, count_reg))

  We prove 4 properties with zero `sorry`, demonstrating that
  Verilog circuits parsed through SVParser can be formally verified.
-/

namespace Sparkle.Verification.CounterProps

-- ============================================================================
-- State and Input types (derived from Verilog ports and registers)
-- ============================================================================

/-- State: one 8-bit register (count_reg) -/
structure Counter8State where
  count_reg : BitVec 8
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Input: rst (active-high reset) and en (count enable) -/
structure Counter8Input where
  rst : BitVec 1
  en  : BitVec 1
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- Next-state function (mirrors IR mux tree)
-- ============================================================================

/-- Next-state transition: mux(rst, 0, mux(en, count+1, count))
    This is the exact structure the SVParser If-Conversion produces. -/
def nextState (s : Counter8State) (i : Counter8Input) : Counter8State :=
  { count_reg :=
      if i.rst == 1 then 0#8
      else if i.en == 1 then s.count_reg + 1
      else s.count_reg }

/-- Output function: count = count_reg (continuous assign in Verilog) -/
def output (s : Counter8State) : BitVec 8 := s.count_reg

-- ============================================================================
-- Formal Properties
-- ============================================================================

/-- Property 1: Counter holds its value when enable is deasserted.
    Verilog: if rst=0 and en=0, count_reg doesn't change. -/
theorem counter_holds_when_disabled (s : Counter8State) :
    nextState s { rst := 0, en := 0 } = s := by
  simp [nextState]

/-- Property 2: Reset always clears the counter to zero.
    Verilog: if rst=1, count_reg <= 0 regardless of en or current value. -/
theorem counter_resets_to_zero (s : Counter8State) (i : Counter8Input) :
    i.rst = 1 → (nextState s i).count_reg = 0#8 := by
  intro h
  simp [nextState, h]

/-- Property 3: Counter increments by 1 when enabled (and not in reset).
    Verilog: if rst=0 and en=1, count_reg <= count_reg + 1. -/
theorem counter_increments (s : Counter8State) :
    (nextState s { rst := 0, en := 1 }).count_reg = s.count_reg + 1 := by
  simp [nextState]

/-- Property 4: Counter wraps around from 255 to 0 (BitVec overflow).
    Demonstrates hardware bit-width semantics: 255 + 1 = 0 in 8-bit. -/
theorem counter_wraps :
    nextState { count_reg := 255#8 } { rst := 0, en := 1 }
    = { count_reg := 0#8 } := by
  native_decide

-- ============================================================================
-- Multi-step properties
-- ============================================================================

/-- Helper: apply n steps of the counter with constant input -/
def nSteps (s : Counter8State) (i : Counter8Input) : Nat → Counter8State
  | 0 => s
  | n + 1 => nextState (nSteps s i n) i

/-- Property 5: After n enabled steps from 0, counter = n mod 256.
    This is the fundamental correctness property of the counter. -/
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
theorem reset_reaches_zero (s : Counter8State) :
    (nSteps s { rst := 1, en := 0 } 1).count_reg = 0#8 := by
  simp [nSteps, nextState]

end Sparkle.Verification.CounterProps
