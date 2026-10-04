/-
  CostDemo — `#verify_cost` smoke test against a few small
  combinational designs.

  Each section presents a known-shape circuit + a budget the
  default cost model should satisfy.  Failures here are
  regressions in the cost analyzer itself (or genuine cost
  growth in the Sparkle compiler's lowering — both worth
  catching at `lake build` time).

  `Budget` fields default to 0, which means "unconstrained"
  for that dimension.  So `{ area := 32 }` is a size-only
  check; `{ depth := 16 }` is a depth-only check; `{ area
  := 32, depth := 16 }` checks both.

  Trade-off framing:
    - **area** = total node cost — talks about *resources*.
      Useful when you have a fixed-size FPGA / ASIC budget,
      or want to detect lowering bloat regressions.
    - **depth** = longest combinational path — talks about
      *speed* under your assumed cost model (frequency-free,
      no target Fmax).  Useful when comparing two implementations
      of the same function, or detecting pipeline regressions.
-/
import Sparkle
import Sparkle.Verification.CostCmd

open Sparkle.Core.Domain Sparkle.Core.Signal

namespace Sparkle.Tests.Verification.CostDemo

abbrev D := defaultDomain

/-! ### Section 1: pure combinational adders. -/

/-- A 16-bit adder.  16 bits × addCost(1) = 16 area, depth 16. -/
def adder16 (a b : Signal D (BitVec 16)) : Signal D (BitVec 16) :=
  (· + ·) <$> a <*> b

#verify_cost adder16 { area := 32 }                  -- size only
#verify_cost adder16 { depth := 32 }                 -- depth only
#verify_cost adder16 { area := 32, depth := 32 }     -- both

/-- An 8-bit XOR. -/
def xor8 (a b : Signal D (BitVec 8)) : Signal D (BitVec 8) :=
  (· ^^^ ·) <$> a <*> b

#verify_cost xor8 { area := 16, depth := 16 }

/-! ### Section 2: detecting bloat regressions.

    `xor8` should fit in area 16.  If the compiler ever
    starts emitting redundant nodes for this pattern, the
    next line will fail `lake build`. -/
#verify_cost xor8 { area := 16 }

/-! ### Section 3: FPGA-fit checks against real parts.

    `tangNano9K` and `tangNano50K` ship Gowin's published
    LUT/FF/BSRAM/DSP ceilings.  These calls confirm the
    estimator runs and that small designs fit trivially. -/

open Sparkle.Verification.Cost.Targets

#verify_fpga adder16 tangNano9K
#verify_fpga xor8 tangNano9K
#verify_fpga adder16 (tangNano9K.withMargin 80)
#verify_fpga adder16 tangNano50K

end Sparkle.Tests.Verification.CostDemo
