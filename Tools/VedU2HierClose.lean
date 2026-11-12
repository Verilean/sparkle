import Lean
import Tools.VedU1Lemmas

/-!
# `ved_hier_close`: the closer of the hierarchical checker's register-step and output goals

The goals are equalities over the (abstracted) register atoms, `%`/`/`/`+`/`*` by literals and `if`s.  Plain
`omega` does not read `^^^` (the `~~~` of a bit is `x ^^^ 1`), so a goal with a negated predicate stayed
open (H2d, R211 and R228: the next value of a counter guarded by `~~~isIdle`).  After the case split the
`^^^`, `|||`, `&&&` operands are numerals again; the literal reductions below evaluate them (the flat
checker's `ved_wide_close` does the same) and `omega` finishes.  The old third alternative (`simp_all`) stays
last.
-/

macro "ved_hier_close" : tactic =>
  `(tactic| first
    | omega
    | ((repeat' split) <;> omega)
    | ((repeat' split) <;>
        (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceDiv, Nat.reduceXor,
          Nat.reduceOr, Nat.reduceAnd, Nat.reduceEqDiff, eq_self, BitVec.toNat_ofNat, Tools.VedU1Lemmas.xor_one_one,
          not_true_eq_false, not_false_eq_true, true_and, and_true, false_and, and_false] at *) <;> omega)
    | ((repeat' split) <;> simp_all <;> omega))
