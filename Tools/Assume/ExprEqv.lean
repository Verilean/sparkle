import Lean
import Sparkle.Core.Domain
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.Assume.ExprEqv, exit 0) on the tree of 237f86d9179ae02cd11f4a9766bcb668fb4bdeab (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source.
-- Assumption module (statements only; no theorems). Written against `scripts/gen5/DG_READERTRACE_FREEZE_REV21.md` (rev21.1) §1.

/-! # Environment/C++ assumption: `==` on `Lean.Expr` is equality when the right side is a domain atom (`EqvAtom`)

**This file holds ONLY an assumption statement** — a `Prop` definition that proofs take as a hypothesis. It is not an
`axiom` and not a theorem. A change here is a change of what is assumed and needs reviewer approval; proof files must
not redefine it.

Design: `scripts/gen5/DG_READERTRACE_FREEZE_REV21.md` §1-§2 (rev21.1, reviewer-approved: type as written there; its truth is NOT approved).

* What is assumed: if `b` has one of the two forms the machine reader writes into its domain slot (`_machIn i` free variable,
  `defaultDomain` constant) and `a == b` is `true`, then `a = b`. `BEq Lean.Expr` is `Lean.Expr.eqv`, an `opaque`
  (`@[extern "lean_expr_eqv"]`), so Lean cannot derive this. It is restricted to a right-hand atom because for general
  expressions `eqv` is alpha equivalence (binder names / binder info are ignored), where `a == b → a = b` is false.
  The left side is arbitrary; the left-only direction is not assumed.
* Basis (a reading, not a proof): upstream `v4.32.1` `src/kernel/expr_eq_fn.cpp` (`lean_expr_eqv` → `expr_eq_fn<false>`:
  `FVar` compares the name, `Const` compares the name and the level list with the structural `level` `operator==`; a different
  `kind` gives `false`) and `Tests/Compiler/ExprEqvAtomTest.lean`.
* Limits: (i) that the binary that runs is built from the read source (only the commit string was checked), (ii) the source of C++
  `name::operator==` was not read, (iii) the treatment of the cached `Level.data` is a premise. Not claimed true.
* Ledger: **T1 +1** when this is registered (expected, not yet counted: reviewer/coder accept it). -/

namespace Tools.Assume.ExprEqv

/-- The two forms of a domain the machine reader accepts (`machDom?`'s two arms), spelled without reference to proof-side definitions. -/
def DomShape (d : Lean.Expr) : Prop :=
  (∃ i : Nat, d = Lean.Expr.fvar ⟨.num (.str .anonymous "_machIn") i⟩) ∨
  (∃ ls : List Lean.Level, d = Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain ls)

/-- **ASSUMPTION `EqvAtom` (T1 +1, expected).** `Expr.eqv` against a right-hand domain atom is equality.
* Domain: every `a : Lean.Expr` and every `b` with `DomShape b`. -/
def EqvAtom : Prop := ∀ a b : Lean.Expr, DomShape b → (a == b) = true → a = b

end Tools.Assume.ExprEqv
