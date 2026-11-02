import Std.Data.HashMap
import Tools.PassPh.Defs
set_option autoImplicit false
-- freeze rev2 + rev3 (scripts/gen5/RT_PASS_PH_FREEZE.md). Built in Pod (kjob lake build Tools.PassPh.Pass Tests.Gen5.PassPhCheck Tools.ShippingGen5ReaderTraceAbbrevS1 Tests.Gen5.ReaderTraceAbbrevS1Check, exit 0) on the tree of 18fa57ac6bdb999e9ac4747bbe7ad43143004dfd (Lean content identical; header comment-only). No sorry / axiom / native_decide in source (all of Tools/PassPh/*.lean). Conditional on BetaNonTargetAgrees, ExprEqvLaws (T1 +1 candidates), HeadBetaAgreesL (replaces T1L-74), RecRulePhU (hypothesis definition); none accepted. Clean build is the coder's. ExprEqvLaws is a hypothesis definition only; no global instance.

namespace Tools.Assume.ExprEqvGL
open Tools.PassPh

/-- `Expr.eqv` (extern) is an alpha equivalence consistent with `hash` that preserves `GL L` (NoPh ∧ BvarLt L).
    NoPh (fvar tag) and BvarLt (bvar index and binder depth) do not depend on binder names. A statement about the C++ implementation. -/
structure ExprEqvLaws : Prop where
  equiv : EquivBEq Lean.Expr
  lawfulHash : LawfulHashable Lean.Expr
  pres : ∀ a b : Lean.Expr, (a == b) = true → ∀ L, GL L a → GL L b

end Tools.Assume.ExprEqvGL
