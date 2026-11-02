import Tools.Assume.ExprEqvGL
set_option autoImplicit false
-- memo lemmas of scripts/gen5/RT_PASS_PH_FREEZE.md rev3 (proofs from RT_PASS_PH_MEMO_scratch.lean.txt). No sorry. Instances are made locally (haveI) from the ExprEqvLaws value; no global instance.

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
