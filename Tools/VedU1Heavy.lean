import Lean
import Tools.VedU1Lemmas

/-!
# Closing tactic for signed select trees (`Tools.VedU1Heavy`)

The wide path of `Tools/VedU1Entry.lean` (data inputs wider than 16 bits in total) rewrites with
`BitVec.toInt_eq_toNat_cond` and `toSigned`, which opens every signed comparison into a case split
on the sign bit of each operand (`x < 128`, `2 * x < 256`).  A tree of `max`-like selects over
signed comparisons then has more case-split conditions than it has comparisons, and the closing
`repeat' split` is exponential in their number (`maxPool2x2`: 7 comparisons, 4 inputs).

`ved_heavy_close` keeps the comparison of two values whole.  Both sides are brought to ONE form:
`toInt` of a `BitVec.ofNat` of an in-range value is `toSigned`, `toNat` / `toInt` are pushed into the
`ite`s, `a < b` is `¬ b ≤ a` and `ite (¬ c)` swaps the branches.  Then `split` takes one case per
distinct comparison (it rewrites every `ite` on the same condition), and each leaf is a linear fact
for `omega` or a `simp_all` closure.  The side conditions (`0 < w`, `a < 2 ^ w`) are discharged by `omega` from the input range facts.

The script is UNTRUSTED: the kernel checks the proof term it produces.
-/

namespace Tools.VedU1Heavy

/-- The closing tactic of the heavy first attempt (see the module docstring). -/
syntax (name := vedHeavyClose) "ved_heavy_close" : tactic

macro_rules
  | `(tactic| ved_heavy_close) =>
    `(tactic| (simp (disch := omega) only [apply_ite BitVec.toNat, apply_ite BitVec.toInt, BitVec.toNat_ofNat,
          Tools.VedU1Lemmas.toInt_ofNat_toSigned, Nat.mod_eq_of_lt, Int.not_le.symm, ite_not]
        <;> (repeat' split)
        <;> (first | omega | (simp_all; done) | (simp_all; omega))))

end Tools.VedU1Heavy
