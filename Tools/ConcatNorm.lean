import Tools.SVParser.RoundtripProof

/-!
  `concatNorm` — reshape an n-ary IR `.concat` into the right-nested
  binary shape that `toCExpr`+`compile` produce, with a proof that it
  preserves `evalExpr`.

  `toCExpr` maps an n-ary `.concat` to nested `CExpr.cat`s (collapsing
  a trailing singleton), and `compile` turns each `cat` back into a
  2-element `.concat`.  So `compile (toCExpr c)`, for a concat-bearing
  cone, is NOT syntactically the elaborated cone `c` — it is `c` with
  every concat right-nested.  A fidelity `rfl` needs the compared
  literal in exactly that shape; `concatNorm c` is it, and
  `norm2_eval` supplies the value equality wherever the capstone reads
  the reshaped cone against the real (flat) one.

  Reuses the concat machinery proven for the roundtrip theorems
  (`restW_eq`, `evalList_length`) from `Tools.SVParser.RoundtripProof`.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics Tools.SVParser.RoundtripProof

namespace Tools.ConcatNorm

def norm2 : List Expr → Expr
  | [] => .concat []
  | [a] => a
  | a :: rest => .concat [a, norm2 rest]

mutual
def concatNorm : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match e with
    | .op o args => .op o (concatNormL fuel args)
    | .concat args => norm2 (concatNormL fuel args)
    | .slice e hi lo => .slice (concatNorm fuel e) hi lo
    | e => e
def concatNormL : Nat → List Expr → List Expr
  | _, [] => []
  | fuel, a :: rest => concatNorm fuel a :: concatNormL fuel rest
end
theorem go_lt (we : WEnv) : ∀ (as : List Expr) (vs : List Nat),
    as.length ≤ vs.length →
    evalExpr.go we as vs < 2 ^ widthOf.go we as := by
  intro as
  induction as with
  | nil => intro vs _; simp [evalExpr.go, widthOf.go]
  | cons a rest ih =>
    intro vs hlen
    cases vs with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [evalExpr.go, widthOf.go]
      rw [restW_eq we rest vrest (by simpa using hlen)]
      have hgo := ih vrest (by simpa using hlen)
      have h1 : (mask (widthOf we a) v) <<< (widthOf.go we rest)
          < 2 ^ (widthOf we a + widthOf.go we rest) := by
        rw [Nat.shiftLeft_eq, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.le_refl _) (Nat.two_pow_pos _)
      have h2 : evalExpr.go we rest vrest
          < 2 ^ (widthOf we a + widthOf.go we rest) :=
        calc evalExpr.go we rest vrest < 2 ^ widthOf.go we rest := hgo
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.or_lt_two_pow h1 h2
theorem concat_pivot (we : WEnv) (env : Env) (a : Expr) (rest : List Expr) :
    evalExpr we env (.concat [a, .concat rest])
      = evalExpr we env (.concat (a :: rest)) := by
  simp only [evalExpr, evalList]
  cases hA : evalExpr we env a with
  | none => simp
  | some va =>
    cases hR : evalList we env rest with
    | none => simp
    | some vs =>
      simp only [hA, hR, Option.bind_some, Option.some_inj,
        Option.bind_eq_bind]
      have hlen : rest.length ≤ vs.length := by rw [evalList_length hR]; exact Nat.le_refl _
      have hfit : mask (widthOf.go we rest) (evalExpr.go we rest vs)
          = evalExpr.go we rest vs :=
        Nat.mod_eq_of_lt (go_lt we rest vs hlen)
      simp only [evalExpr.go, List.zip_cons_cons, List.foldl_cons,
        List.foldl_nil, List.zip_nil_right, widthOf, widthOf.go,
        Nat.zero_add, Nat.add_zero, Nat.shiftLeft_zero, Nat.or_zero,
        hfit, restW_eq we rest vs hlen]

theorem norm2_width (we : WEnv) : ∀ (a b : Expr) (rest : List Expr),
    widthOf we (norm2 (a :: b :: rest))
      = widthOf we (.concat (a :: b :: rest))
  | _, _, [] => rfl
  | a, b, c :: rest => by
    show widthOf we (.concat [a, norm2 (b :: c :: rest)])
      = widthOf we (.concat (a :: b :: c :: rest))
    simp only [widthOf, widthOf.go, norm2_width we b c rest]
    omega

/-- For ≥2 elements, `norm2` preserves concat semantics.  (A singleton
    collapses to a bare, unmasked element; it is only ever produced
    NESTED inside a `cat`/2-concat, which re-masks — never a top-level
    concat of a real cone, which always has ≥2 elements.) -/
theorem norm2_eval (we : WEnv) (env : Env) :
    ∀ (a b : Expr) (rest : List Expr),
      evalExpr we env (norm2 (a :: b :: rest))
        = evalExpr we env (.concat (a :: b :: rest))
  | _, _, [] => rfl
  | a, b, c :: rest => by
    have ih := norm2_eval we env b c rest
    have ihw := norm2_width we b c rest
    rw [← concat_pivot we env a (b :: c :: rest)]
    show evalExpr we env (.concat [a, norm2 (b :: c :: rest)])
      = evalExpr we env (.concat [a, .concat (b :: c :: rest)])
    -- unfold ONE concat layer, then match the element eval by ih (as a
    -- rewrite so norm2 is not unfolded underneath) and the node width
    -- by ihw
    have hlist : evalList we env [a, norm2 (b :: c :: rest)]
        = evalList we env [a, .concat (b :: c :: rest)] := by
      simp only [evalList, ih]
    rw [show evalExpr we env (.concat [a, norm2 (b :: c :: rest)])
          = ((evalList we env [a, norm2 (b :: c :: rest)]).bind
              fun vals => some (evalExpr.go we
                [a, norm2 (b :: c :: rest)] vals)) from rfl]
    rw [show evalExpr we env (.concat [a, .concat (b :: c :: rest)])
          = ((evalList we env [a, .concat (b :: c :: rest)]).bind
              fun vals => some (evalExpr.go we
                [a, .concat (b :: c :: rest)] vals)) from rfl]
    rw [hlist]
    -- both sides now: evalList … .bind (go [a, ·]).  The go-combiner
    -- reads widthOf of the 2nd element; ihw makes those agree.
    cases evalList we env [a, .concat (b :: c :: rest)] with
    | none => rfl
    | some vals =>
      -- go [a, X] vals reads widthOf X only in the offset; ihw makes
      -- the two X's widths agree, so the assembled values match
      simp only [Option.bind_some, Option.some_inj]
      cases vals with
      | nil => rfl
      | cons v0 vs0 =>
        cases vs0 with
        | nil => simp only [evalExpr.go, List.zip_cons_cons,
            List.zip_nil_right, List.foldl_cons, List.foldl_nil]
        | cons v1 vs1 =>
          simp only [evalExpr.go, List.zip_cons_cons,
            List.zip_nil_right, List.foldl_cons, List.foldl_nil,
            widthOf.go, ihw]

end Tools.ConcatNorm
