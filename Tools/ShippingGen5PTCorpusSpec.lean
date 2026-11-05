import Tools.ShippingGen5PTCorpus
import Tools.ShippingGen5DepRows
set_option autoImplicit false
/-! # Spec supply for `PTcorpus` (issue sparkle-ledger-dd4-deprows, Q-C; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Spec)

No TRUSTED, axiom, `sorry`, `native_decide`. Existing files are unchanged. A Spec being STATED does not pay a row: a row is counted only when a theorem `RowTypedAtV PTcorpus env c ls` / `RowTeleEvAt PTcorpus env c ls` exists
(its env facts stay hypotheses, evaluated in the real environment by the Check).

* §1 The result type former applied to the first `m` binders (`D x₁ … x_m`, any `m`): `instForallS_spine` (a generalisation of `instForallS_depFirst`, which is `m = 1`) and `rowTypedAtV_spine`.
* §2 `PTcorpus` supplies the Spec per key.
* §3 The 26 keys of `DepRows` have no row in `PTcorpus` (`notImportable`): `FirstArgSpec` / `DomFieldsSpec` cannot be supplied, proved. -/
namespace Tools.ShippingGen5PTCorpusSpec
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV Tools.ShippingGen5PTCorpus

/-- The first `m` of `n` binders as loose bound variables: `bvar (n-1), …, bvar (n-m)` (meaningful for `m ≤ n`). -/
def spine : Nat → Nat → List Expr
  | _, 0 => []
  | 0, _ + 1 => []
  | n + 1, m + 1 => .bvar n :: spine n m

theorem spine_lt : ∀ (n m : Nat), m ≤ n → ∀ e ∈ spine n m, ∃ j, j < n ∧ e = .bvar j
  | _, 0, _, e, he => by simp [spine] at he
  | 0, m + 1, h, _, _ => by omega
  | n + 1, m + 1, h, e, he => by
    simp only [spine, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨n, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := spine_lt n m (by omega) e he
      exact ⟨j, by omega, rfl⟩

theorem substS_spine (n m : Nat) (h : m ≤ n) (x : Expr) : (spine n m).map (fun e => substS e n x) = spine n m := by
  refine (List.map_congr_left (g := fun e => e) fun e he => ?_).trans (List.map_id _)
  obtain ⟨j, hj, rfl⟩ := spine_lt n m h e he
  simp [substS, hj]

/-- `instForallS` of `n` binders whose result is `D` applied to `pre` (already substituted, lifted) and then to the first `m` binders: `D (pre ++ args.take m)`. -/
theorem instForallS_spine (D : Name) (Ls : List Level) :
    ∀ (n m : Nat) (T : Expr) (pre args : List Expr), m ≤ n →
      PiN T n (mkAppN (.const D Ls) (pre.map (fun e => liftS e 0 n) ++ spine n m).toArray) → args.length = n →
      instForallS T args = mkAppN (.const D Ls) (pre ++ args.take m).toArray
  | 0, m, T, pre, args, hm, h, hl => by
    have : args = [] := List.length_eq_zero_iff.mp hl
    subst this
    have hm0 : m = 0 := by omega
    subst hm0
    have h' : T = mkAppN (.const D Ls) (pre.map (fun e => liftS e 0 0) ++ spine 0 0).toArray := h
    rw [instForallS_nil, h']
    simp [spine, liftS_zero]
  | n + 1, m, T, pre, args, hm, ⟨y, A, B, bi, hT, hB⟩, hl => by
    subst hT
    match args, hl with
    | b :: xs, hl =>
      have hl' : xs.length = n := by simpa using hl
      show instForallS (substS B 0 b) xs = _
      have h1 := piN_substS n B _ 0 b hB
      rw [Nat.zero_add, substS_mkAppN] at h1
      have hc : substS (.const D Ls) n b = .const D Ls := rfl
      rw [hc] at h1
      have hpre : (pre.map (fun e => liftS e 0 (n + 1))).map (fun e => substS e n b) = pre.map (fun e => liftS e 0 n) := by
        rw [List.map_map]
        exact List.map_congr_left fun e _ => substS_liftS_in e 0 (n + 1) n b (by omega) (by omega)
      cases m with
      | zero =>
        rw [List.map_append, hpre] at h1
        have := instForallS_spine D Ls n 0 _ pre xs (by omega) (by simpa [spine] using h1) hl'
        simpa using this
      | succ m =>
        have h2 : (pre.map (fun e => liftS e 0 (n + 1)) ++ spine (n + 1) (m + 1)).map (fun e => substS e n b) =
            (pre ++ [b]).map (fun e => liftS e 0 n) ++ spine n m := by
          rw [List.map_append, hpre]
          simp only [spine, List.map_cons, substS, Nat.lt_irrefl, if_false, if_true, List.map_append, List.map_nil]
          rw [substS_spine n m (by omega) b]
          simp
        rw [h2] at h1
        have := instForallS_spine D Ls n m _ (pre ++ [b]) xs (by omega) h1 hl'
        simpa using this

end Tools.ShippingGen5PTCorpusSpec
