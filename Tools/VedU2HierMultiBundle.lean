import Sparkle.IR.Semantics
import Tools.VedU2HierNet

/-!
# H3-open: the value of a wire that reads one register out of the parent's register BUNDLE

`circuit do` bundles the parent's registers into one wire (`concat` of the register outputs, MSB first, then an alias
`loop` wire) and reads each register through a `slice` of it.  A parent with 34 registers of 64 bits has a 2000-bit
bundle: evaluating the slice by unfolding the concatenation into `Nat` arithmetic (the proof of the instance's
argument net, H2c) costs more than the rest of the proof.  `bundle_slice_fact` says it once: the slice that is
exactly the `k`-th element of the concatenation of `names` has the value of that element.  The entry's script checks
the premises (`asgOf`, the offsets) by `decide`.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics

namespace Tools.VedU2HierMulti

def W (we : WEnv) (names : List String) : Nat := (names.map we).foldl (· + ·) 0

theorem foldl_add_g {α : Type} (g : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc p => acc + g p) a = a + l.foldl (fun acc p => acc + g p) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (a + g x), ih (0 + g x)]; omega

theorem foldl_add_aux (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  have := foldl_add_g (fun x : Nat => x) l a
  simpa using this

theorem W_cons (we : WEnv) (n : String) (ns : List String) : W we (n :: ns) = we n + W we ns := by
  unfold W
  simp only [List.map_cons, List.foldl_cons]
  rw [foldl_add_aux]; omega

theorem zipW (we : WEnv) (ns : List String) (vs : List Nat) (hl : ns.length = vs.length) :
    ((ns.map Expr.ref).zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we p.1) 0 = W we ns := by
  induction ns generalizing vs with
  | nil => cases vs <;> simp [W]
  | cons n ns ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [foldl_add_g (fun p : Expr × Nat => widthOf we p.1), ih vs hl, W_cons]
      simp [widthOf]

theorem go_cons (we : WEnv) (n : String) (ns : List String) (v : Nat) (vs : List Nat) (hl : ns.length = vs.length) :
    evalExpr.go we (Expr.ref n :: ns.map Expr.ref) (v :: vs)
      = (mask (we n) v) <<< W we ns ||| evalExpr.go we (ns.map Expr.ref) vs := by
  rw [evalExpr.go]
  rw [← zipW we ns vs hl]
  simp [widthOf]

theorem go_lt (we : WEnv) (ns : List String) (vs : List Nat) (hl : ns.length = vs.length) :
    evalExpr.go we (ns.map Expr.ref) vs < 2 ^ W we ns := by
  induction ns generalizing vs with
  | nil => cases vs <;> simp [W, evalExpr.go]
  | cons n ns ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [List.map_cons, go_cons we n ns v vs hl, W_cons]
      have h1 := ih vs hl
      have h2 : mask (we n) v < 2 ^ we n := Nat.mod_lt _ (Nat.two_pow_pos _)
      rw [← Nat.shiftLeft_add_eq_or_of_lt h1, Nat.shiftLeft_eq, Nat.pow_add]
      calc mask (we n) v * 2 ^ W we ns + evalExpr.go we (ns.map Expr.ref) vs
          < mask (we n) v * 2 ^ W we ns + 2 ^ W we ns := by omega
        _ = (mask (we n) v + 1) * 2 ^ W we ns := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ 2 ^ we n * 2 ^ W we ns := Nat.mul_le_mul_right _ h2


theorem mod_aux (M B C y : Nat) : (M * (B * C) + y) % B = y % B := by
  rw [Nat.mul_left_comm, Nat.mul_add_mod]

theorem W_drop_le (we : WEnv) (ns : List String) (k : Nat) (hk : k < ns.length) :
    W we (ns.drop (k + 1)) + we ns[k] ≤ W we ns := by
  induction ns generalizing k with
  | nil => simp at hk
  | cons n ns ih =>
    cases k with
    | zero => simp [W_cons]; omega
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      have := ih k hk
      simp only [List.drop_succ_cons, List.getElem_cons_succ, W_cons]
      omega

theorem go_slice (we : WEnv) (ns : List String) (vs : List Nat) (hl : ns.length = vs.length) (k : Nat)
    (hk : k < ns.length) :
    (evalExpr.go we (ns.map Expr.ref) vs >>> W we (ns.drop (k + 1))) % 2 ^ we ns[k]
      = vs[k]'(hl ▸ hk) % 2 ^ we ns[k] := by
  induction ns generalizing vs k with
  | nil => simp at hk
  | cons n ns ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [List.map_cons, go_cons we n ns v vs hl]
      have hg := go_lt we ns vs hl
      rw [← Nat.shiftLeft_add_eq_or_of_lt hg, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      cases k with
      | zero =>
        simp only [List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero, List.getElem_cons_zero]
        have : (mask (we n) v * 2 ^ W we ns + evalExpr.go we (ns.map Expr.ref) vs) / 2 ^ W we ns = mask (we n) v := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hg]; simp
        rw [this]; simp [mask]
      | succ k =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
        simp only [List.drop_succ_cons, List.getElem_cons_succ]
        have ih' := ih vs hl k hk
        have hle := W_drop_le we ns k hk
        -- (m * 2^Wns + g) / 2^s = m * 2^(Wns - s) + g / 2^s
        obtain ⟨d, hd⟩ : ∃ d, W we ns = W we (ns.drop (k + 1)) + we ns[k] + d := ⟨W we ns - (W we (ns.drop (k + 1)) + we ns[k]), by omega⟩
        rw [Nat.shiftRight_eq_div_pow] at ih'
        have e1 : 2 ^ W we ns = 2 ^ W we (ns.drop (k + 1)) * (2 ^ we ns[k] * 2 ^ d) := by
          rw [hd, Nat.pow_add, Nat.pow_add, Nat.mul_assoc]
        have hA : 0 < 2 ^ W we (ns.drop (k + 1)) := Nat.two_pow_pos _
        have e2 : (mask (we n) v * 2 ^ W we ns + evalExpr.go we (ns.map Expr.ref) vs) / 2 ^ W we (ns.drop (k + 1))
            = mask (we n) v * (2 ^ we ns[k] * 2 ^ d) + evalExpr.go we (ns.map Expr.ref) vs / 2 ^ W we (ns.drop (k + 1)) := by
          rw [e1, Nat.mul_left_comm, Nat.mul_add_div hA]
        rw [e2]
        exact (mod_aux _ _ _ _).trans ih'


theorem evalList_refs (we : WEnv) (env : Env) (ns : List String) :
    evalList we env (ns.map Expr.ref) = some (ns.map env) := by
  induction ns with
  | nil => simp [evalList]
  | cons n ns ih => simp [evalList, evalExpr, ih]

theorem eval_concat_refs (we : WEnv) (env : Env) (ns : List String) :
    evalExpr we env (.concat (ns.map Expr.ref)) = some (evalExpr.go we (ns.map Expr.ref) (ns.map env)) := by
  simp [evalExpr, evalList_refs]

/-- A slice of the concatenation of wires that is exactly one of them. -/
theorem slice_concat_val (we : WEnv) (E : Env) (names : List String) (k : Nat) (hk : k < names.length)
    (V hi lo : Nat) (hv : evalExpr we E (.concat (names.map Expr.ref)) = some V)
    (hlo : lo = W we (names.drop (k + 1))) (hhi : hi + 1 = lo + we names[k])
    (hw0 : 0 < we names[k]) (hrange : E names[k] < 2 ^ we names[k]) : mask (hi - lo + 1) (V >>> lo) = E names[k] := by
  rw [eval_concat_refs] at hv
  cases hv
  have hlen : names.length = (names.map E).length := by simp
  have := go_slice we names (names.map E) hlen k hk
  have hw : hi - lo + 1 = we names[k] := by omega
  rw [hw]
  subst hlo
  simp only [List.getElem_map] at this
  unfold mask
  rw [this]
  exact Nat.mod_eq_of_lt hrange


/-- The value of the wire `w`, `slice (ref x) hi lo` with `x` an alias of the concatenation wire `y`, is the value of the
element it spans. -/
theorem bundle_slice_fact (we : WEnv) (b0 : List Stmt) (E : Env)
    (hasg : ∀ l r, Tools.VedU2Hier.asgOf b0 l = some r → evalExpr we E r = some (E l))
    (w x y : String) (hi lo : Nat) (names : List String) (k : Nat) (hk : k < names.length)
    (hw : Tools.VedU2Hier.asgOf b0 w = some (.slice (.ref x) hi lo)) (hEx : E x = E y)
    (hy : Tools.VedU2Hier.asgOf b0 y = some (.concat (names.map Expr.ref)))
    (hlo : lo = W we (names.drop (k + 1))) (hhi : hi + 1 = lo + we names[k])
    (hw0 : 0 < we names[k]) (hrange : E names[k] < 2 ^ we names[k]) : E w = E names[k] := by
  have h1 := hasg w _ hw
  have h2 := hasg y _ hy
  simp only [evalExpr] at h1
  rw [hEx] at h1
  have h3 := slice_concat_val we E names k hk (E y) hi lo h2 hlo hhi hw0 hrange
  simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h1
  rw [← h1]
  exact h3


/-- The value of a concatenation wire is below `2 ^` the sum of the elements' widths (every element is masked). -/
theorem concat_range (we : WEnv) (b0 : List Stmt) (E : Env)
    (hasg : ∀ l r, Tools.VedU2Hier.asgOf b0 l = some r → evalExpr we E r = some (E l))
    (B : String) (names : List String) (hB : Tools.VedU2Hier.asgOf b0 B = some (.concat (names.map Expr.ref)))
    (hw : we B = W we names) : E B < 2 ^ we B := by
  have h := hasg B _ hB
  rw [eval_concat_refs] at h
  have h2 := Option.some.inj h
  rw [hw, ← h2]
  exact go_lt we names (names.map E) (by simp)

end Tools.VedU2HierMulti
