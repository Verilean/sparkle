import Tools.VedU1Loop
import Tools.VedU1SmallReg

/-! # Iir: one syntactic copy of a wide product before `omega`

`IP.Control.IIRBiquad` (R101, R112): the fixed-point product `k * sext x >> 16` reaches the closing goal in several
syntactic copies (the `Nat` form of the implementation and the `Int` form of the signed specification, `bmod`
of a sum, ...).  `omega` gives every copy its own floor atoms and, without dark shadows, cannot identify them.
`ved_iir_norm` rewrites the `Nat` hypotheses and the goal into `Int`, folds the literal casts and the
`% 2^w` of a bounded value, so the copies coincide. -/
namespace Tools.VedU1Iir

/-- the high half of an `Int` concatenation `(x % m) * m + y % m` is `x % m`. -/
theorem int_concat_div (x y m : Int) (hm : 0 < m) : (x % m * m + y % m) / m = x % m := by
  rw [Int.add_comm, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hm),
    Int.ediv_eq_zero_of_lt (Int.emod_nonneg _ (Int.ne_of_gt hm)) (Int.emod_lt_of_pos _ hm), Int.zero_add]

/-- `ved_iir_norm`: the `Nat` facts and goal as `Int`, literal casts folded, `% 2^w` of a bounded value removed. -/
syntax (name := vedIirNorm) "ved_iir_norm" : tactic

macro_rules
  | `(tactic| ved_iir_norm) =>
    `(tactic| ((try simp only [← Int.ofNat_lt, ← Int.ofNat_le] at *) <;>
      (try refine Int.ofNat.inj ?_) <;>
      (try simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_emod, Int.natCast_ediv, Int.cast_ofNat_Int,
        Int.ofNat_eq_natCast, Int.reduceMod, Int.reduceMul, Int.reduceAdd, Int.bmod_def] at *) <;>
      (try simp (disch := omega) only [int_concat_div, Int.emod_eq_of_lt, Int.reduceMod, Int.reduceMul, Int.reduceAdd] at *) <;>
      (try simp only [Int.bmod_def] at *)))

end Tools.VedU1Iir
