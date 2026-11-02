import Std.Data.HashMap
import Tools.PassPh.Defs
set_option autoImplicit false
-- ExprEqvLaws as in scripts/gen5/RT_PASS_PH_FREEZE.md rev3 (reviewer-approved as a design, b74a86de). A hypothesis definition only: not an accepted premise, not counted in the ledger (conditional T1 +1 candidate). No global instance.

namespace Tools.Assume.ExprEqvGL
open Tools.PassPh

/-- `Expr.eqv` (extern) is an alpha equivalence consistent with `hash` that preserves `GL L` (NoPh ∧ BvarLt L).
    NoPh (fvar tag) and BvarLt (bvar index and binder depth) do not depend on binder names. A statement about the C++ implementation. -/
structure ExprEqvLaws : Prop where
  equiv : EquivBEq Lean.Expr
  lawfulHash : LawfulHashable Lean.Expr
  pres : ∀ a b : Lean.Expr, (a == b) = true → ∀ L, GL L a → GL L b

end Tools.Assume.ExprEqvGL
