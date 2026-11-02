import Tools.Assume.ExprEqvGL
set_option autoImplicit false
-- freeze rev2 + rev3 (scripts/gen5/RT_PASS_PH_FREEZE.md). Built in Pod (kjob lake build Tools.PassPh.Pass Tests.Gen5.PassPhCheck Tools.ShippingGen5ReaderTraceAbbrevS1 Tests.Gen5.ReaderTraceAbbrevS1Check, exit 0) on the tree of 18fa57ac6bdb999e9ac4747bbe7ad43143004dfd (Lean content identical; header comment-only). No sorry / axiom / native_decide in source (all of Tools/PassPh/*.lean). Conditional on BetaNonTargetAgrees, ExprEqvLaws (T1 +1 candidates), HeadBetaAgreesL (replaces T1L-74), RecRulePhU (hypothesis definition); none accepted. Clean build is the coder's.

namespace Tools.PassPh
open Tools.Assume.ExprEqvGL

theorem memoGoodL_empty : MemoGoodL (∅ : Std.HashMap Lean.Expr Lean.Expr) := by
  intro k v h; simp at h

theorem memoGoodL_insert (hEq : ExprEqvLaws)
    {s : Std.HashMap Lean.Expr Lean.Expr} (hs : MemoGoodL s) (e r : Lean.Expr) (hr : ∀ L, GL L e → GL L r) :
    MemoGoodL (s.insert e r) := by
  haveI := hEq.equiv
  haveI := hEq.lawfulHash
  intro k v h L hk
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hb
    have : (k == e) = true := BEq.symm hb
    cases h
    exact hr L (hEq.pres k e this L hk)
  · exact hs k v (by rwa [Std.HashMap.get?_eq_getElem?]) L hk

theorem memoGoodL_hit {s : Std.HashMap Lean.Expr Lean.Expr} (hs : MemoGoodL s) {e v : Lean.Expr}
    (h : s.get? e = some v) : ∀ L, GL L e → GL L v := hs e v h

end Tools.PassPh
