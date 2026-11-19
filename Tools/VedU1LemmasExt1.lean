/-
  Bundle `unsolved` (U1 coverage): lemmas for the generated closers of the loop script, found by
  printing the unsolved goals of real-IP rows.  Used only by untrusted scripts (the kernel checks
  the result), by name from the closing tactic of `loopScriptFor`.
-/
import Lean

namespace Tools.VedU1LemmasExt1

/-- the `Bool` comparison of a `BitVec` test with a `Nat` input bit (`topBit ^^ bitIn` of a CRC
register, after the `^^` of `Bool` became `=`) as an iff of propositions -/
theorem beq_eq_bne {w : Nat} (a b : BitVec w) (c : Nat) :
    (((a == b) = (c != 0)) ↔ ((a = b) ↔ c ≠ 0)) := by
  cases h : (a == b) <;> cases h2 : (c != 0) <;> simp_all

end Tools.VedU1LemmasExt1
