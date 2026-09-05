import Tools.ConeFold
import Tools.ConcatNorm

/-!
  The seam, slice-resolution half.

  `#verify_elab` / `#verify_elab_deep` run each cone through
  `Tools.VerifyElab.resolveSlicesW` (slice-of-concat window collapse,
  identity-slice collapse, slice-of-slice fusion) before goal
  generation.  For the seam this pass, like `inlineCone`
  (Tools/ConeFold.lean), needs an object-level twin plus a
  semantic-preservation theorem, so the composed statement speaks about
  the expression that actually lands in the generated goals.

  The twin is fuel-primary (the shipping recursion re-enters itself
  with REBUILT slice expressions, so no structural measure exists) and
  adds two soundness guards the shipping function omits because its
  inputs never violate them (checked by the `#guard` probes below):

  * window acceptance requires `0 < w ∧ lo ≤ hi` (no zero-width parts,
    no degenerate windows);
  * slice-of-slice fusion requires the outer window to fit inside the
    inner slice and be non-degenerate (`ilo + hi ≤ ihi ∧ lo ≤ hi`) —
    the shipping comment asserts the containment always holds; the twin
    enforces both.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics

namespace Tools.ConeFold

section ResolveSlices


/- ---- reduction lemmas ----
   The (fuel+1, .slice (.concat …)) pattern OVERLAPS the general
   (fuel+1, .slice e …) pattern, so with an abstract slice operand the
   compiled match is stuck (it must test the operand's constructor
   first).  These lemmas restore per-shape reduction; each is `rfl`
   once the operand constructor is concrete (Session 11c's recipe). -/

theorem rsT_zero (wt : Std.HashMap String Nat) (e : Expr) :
    resolveSlicesT wt 0 e = e := by
  rw [resolveSlicesT.eq_def]

theorem rsT_op (wt : Std.HashMap String Nat) (fuel : Nat) (o : Operator)
    (args : List Expr) :
    resolveSlicesT wt (fuel + 1) (.op o args)
      = .op o (resolveSlicesTL wt fuel args) := by
  rw [resolveSlicesT.eq_def]

theorem rsT_concat (wt : Std.HashMap String Nat) (fuel : Nat)
    (args : List Expr) :
    resolveSlicesT wt (fuel + 1) (.concat args)
      = .concat (resolveSlicesTL wt fuel args) := by
  rw [resolveSlicesT.eq_def]

theorem rsT_slice_concat (wt : Std.HashMap String Nat) (fuel : Nat)
    (parts0 : List Expr) (hi lo : Nat) :
    resolveSlicesT wt (fuel + 1) (.slice (.concat parts0) hi lo)
      = (match (resolveSlicesTL wt fuel (flattenL parts0)).mapM
            (widthOfPartT wt) with
        | none =>
          .slice (.concat (resolveSlicesTL wt fuel (flattenL parts0))) hi lo
        | some ws =>
          match findWindow hi lo (resolveSlicesTL wt fuel (flattenL parts0))
              ws (ws.foldl (· + ·) 0) with
          | some r => r
          | none =>
            .slice (.concat (resolveSlicesTL wt fuel (flattenL parts0)))
              hi lo) := by
  rw [resolveSlicesT.eq_def]; rfl

theorem rsT_slice_reduce (wt : Std.HashMap String Nat) (fuel : Nat)
    (e : Expr) (hi lo : Nat) (hne : ∀ ps, e ≠ Expr.concat ps) :
    resolveSlicesT wt (fuel + 1) (.slice e hi lo)
      = (match resolveSlicesT wt fuel e with
        | .concat parts =>
          resolveSlicesT wt fuel (.slice (.concat parts) hi lo)
        | .ref n =>
          if lo == 0 && wt.get? n == some (hi + 1) then .ref n
          else .slice (.ref n) hi lo
        | .slice inner ihi ilo =>
          if ilo + hi ≤ ihi ∧ lo ≤ hi then
            resolveSlicesT wt fuel (.slice inner (ilo + hi) (ilo + lo))
          else .slice (.slice inner ihi ilo) hi lo
        | e' => .slice e' hi lo) := by
  cases e with
  | concat ps => exact absurd rfl (hne ps)
  | const v w => rw [resolveSlicesT.eq_def]; rfl
  | ref n => rw [resolveSlicesT.eq_def]; rfl
  | op o args => rw [resolveSlicesT.eq_def]; rfl
  | slice i a b => rw [resolveSlicesT.eq_def]; rfl
  | sliceDim i d j => rw [resolveSlicesT.eq_def]; rfl
  | index a i => rw [resolveSlicesT.eq_def]; rfl

theorem rsT_const (wt : Std.HashMap String Nat) (fuel : Nat) (v : Int)
    (w : Nat) : resolveSlicesT wt (fuel + 1) (.const v w) = .const v w := by
  rw [resolveSlicesT.eq_def]

theorem rsT_ref (wt : Std.HashMap String Nat) (fuel : Nat) (n : String) :
    resolveSlicesT wt (fuel + 1) (.ref n) = .ref n := by
  rw [resolveSlicesT.eq_def]

theorem rsT_sliceDim (wt : Std.HashMap String Nat) (fuel : Nat) (e : Expr)
    (d i : Sparkle.IR.Type.DimExpr) :
    resolveSlicesT wt (fuel + 1) (.sliceDim e d i) = .sliceDim e d i := by
  rw [resolveSlicesT.eq_def]

theorem rsT_index (wt : Std.HashMap String Nat) (fuel : Nat) (a i : Expr) :
    resolveSlicesT wt (fuel + 1) (.index a i) = .index a i := by
  rw [resolveSlicesT.eq_def]

theorem rsTL_nil (wt : Std.HashMap String Nat) (fuel : Nat) :
    resolveSlicesTL wt fuel [] = [] := by
  rw [resolveSlicesTL.eq_def]

theorem rsTL_cons (wt : Std.HashMap String Nat) (fuel : Nat) (a : Expr)
    (rest : List Expr) :
    resolveSlicesTL wt fuel (a :: rest)
      = resolveSlicesT wt fuel a :: resolveSlicesTL wt fuel rest := by
  rw [resolveSlicesTL.eq_def]

/- ---- arithmetic helper kit (private re-proofs; the originals live in
        Tools/SVParser/{RoundtripProof,EmitSem}.lean as private or
        differently-shaped statements) ---- -/

theorem or_shiftLeft (a b k : Nat) :
    (a ||| b) <<< k = a <<< k ||| b <<< k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_or]
  by_cases h : k ≤ i <;> simp [h]

theorem zipFold_width (we : WEnv) :
    ∀ (as : List Expr) (vs : List Nat), as.length ≤ vs.length →
    ∀ acc, ((as.zip vs).foldl (fun a (p : Expr × Nat) =>
        a + widthOf we p.1) acc) = acc + widthOf.go we as
  | [], _, _, acc => by simp [widthOf.go]
  | a :: as', vs, hlen, acc => by
    cases vs with
    | nil => simp at hlen
    | cons v vs' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [zipFold_width we as' vs' (by simpa using hlen)]
      simp [widthOf.go]; omega

theorem evalList_len {we : WEnv} {env : Env} :
    ∀ {args : List Expr} {vs : List Nat},
      evalList we env args = some vs → vs.length = args.length
  | [], vs, h => by simp [evalList] at h; simp [← h]
  | a :: rest, vs, h => by
    simp only [evalList, Option.bind_eq_bind] at h
    cases hA : evalExpr we env a with
    | none => rw [hA] at h; simp at h
    | some v =>
      rw [hA] at h
      cases hR : evalList we env rest with
      | none => rw [hR] at h; simp at h
      | some vs' =>
        rw [hR] at h; simp only [Option.bind_some] at h
        cases h; simp [evalList_len hR]

theorem go_lt (we : WEnv) :
    ∀ (args : List Expr) (vals : List Nat), args.length = vals.length →
      evalExpr.go we args vals < 2 ^ widthOf.go we args
  | [], _, _ => by simp [evalExpr.go, widthOf.go]
  | a :: rest, vals, hlen => by
    cases vals with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [evalExpr.go, widthOf.go]
      rw [zipFold_width we rest vrest (by simp at hlen; omega)]
      simp only [Nat.zero_add]
      have h1 : mask (widthOf we a) v < 2 ^ widthOf we a :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : mask (widthOf we a) v <<< widthOf.go we rest
          < 2 ^ (widthOf we a + widthOf.go we rest) := by
        rw [Nat.shiftLeft_eq, Nat.pow_add]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
      have h3 : evalExpr.go we rest vrest
          < 2 ^ (widthOf we a + widthOf.go we rest) :=
        Nat.lt_of_lt_of_le (go_lt we rest vrest (by simp at hlen; omega))
          (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.or_lt_two_pow h2 h3

theorem widthgo_append (we : WEnv) :
    ∀ (xs ys : List Expr),
      widthOf.go we (xs ++ ys) = widthOf.go we xs + widthOf.go we ys
  | [], ys => by simp [widthOf.go]
  | x :: xs', ys => by
    simp only [List.cons_append, widthOf.go, widthgo_append we xs' ys]
    omega

theorem go_append (we : WEnv) :
    ∀ (xs ys : List Expr) (va vb : List Nat),
      va.length = xs.length → vb.length = ys.length →
      evalExpr.go we (xs ++ ys) (va ++ vb)
        = evalExpr.go we xs va <<< widthOf.go we ys ||| evalExpr.go we ys vb
  | [], ys, va, vb, hva, _ => by
    have : va = [] := List.length_eq_zero_iff.mp (by simpa using hva)
    subst this
    simp [evalExpr.go, widthOf.go, Nat.zero_shiftLeft]
  | x :: xs', ys, va, vb, hva, hvb => by
    cases va with
    | nil => simp at hva
    | cons v va' =>
      simp only [List.cons_append, evalExpr.go]
      have hlen1 : (xs' ++ ys).length ≤ (va' ++ vb).length := by
        simp at hva ⊢; omega
      have hlen2 : xs'.length ≤ va'.length := by simp at hva; omega
      rw [zipFold_width we (xs' ++ ys) (va' ++ vb) hlen1,
          zipFold_width we xs' va' hlen2,
          go_append we xs' ys va' vb (by simp at hva; omega) hvb,
          widthgo_append we xs' ys]
      simp only [Nat.zero_add]
      rw [or_shiftLeft, Nat.or_assoc]
      congr 1
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
          Nat.pow_add, ← Nat.mul_assoc]

theorem evalList_append {we : WEnv} {env : Env} :
    ∀ {xs ys : List Expr} {va vb : List Nat},
      evalList we env xs = some va → evalList we env ys = some vb →
      evalList we env (xs ++ ys) = some (va ++ vb)
  | [], _, va, _, hx, hy => by
    simp [evalList] at hx; subst hx; simpa using hy
  | x :: xs', ys, va, vb, hx, hy => by
    simp only [evalList, Option.bind_eq_bind] at hx
    cases hX : evalExpr we env x with
    | none => rw [hX] at hx; simp at hx
    | some v =>
      rw [hX] at hx
      cases hXs : evalList we env xs' with
      | none => rw [hXs] at hx; simp at hx
      | some va' =>
        rw [hXs] at hx; simp only [Option.bind_some] at hx
        cases hx
        simp only [List.cons_append, evalList, Option.bind_eq_bind, hX,
          evalList_append hXs hy, Option.bind_some]

/- ---- widths of parts, flattening, and window search ---- -/

theorem widthOfPartT_width (we : WEnv) (wt : Std.HashMap String Nat)
    (hwt : ∀ n w, wt.get? n = some w → we n = w) :
    ∀ (p : Expr) (w : Nat), widthOfPartT wt p = some w → widthOf we p = w
  | .const .., w, h => by
    simp only [widthOfPartT, Option.some_inj] at h; simp [widthOf, h]
  | .ref n, w, h => by
    simp only [widthOfPartT] at h; simp [widthOf, hwt n w h]
  | .slice .., w, h => by
    simp only [widthOfPartT, Option.some_inj] at h; simp [widthOf, h]
  | .op .., _, h => by simp [widthOfPartT] at h
  | .concat .., _, h => by simp [widthOfPartT] at h
  | .sliceDim .., _, h => by simp [widthOfPartT] at h
  | .index .., _, h => by simp [widthOfPartT] at h

theorem widthOfPartT_masked (we : WEnv) (env : Env)
    (wt : Std.HashMap String Nat)
    (hwt : ∀ n w, wt.get? n = some w → we n = w)
    (hb : ∀ n, env n < 2 ^ we n) :
    ∀ (p : Expr) (w : Nat), widthOfPartT wt p = some w →
    ∀ u, evalExpr we env p = some u → u < 2 ^ w
  | .const v cw, w, h, u, he => by
    simp only [widthOfPartT, Option.some_inj] at h; subst h
    simp only [evalExpr, Option.some_inj] at he
    subst he; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | .ref n, w, h, u, he => by
    simp only [widthOfPartT] at h
    simp only [evalExpr, Option.some_inj] at he
    subst he; rw [← hwt n w h]; exact hb n
  | .slice p hi lo, w, h, u, he => by
    simp only [widthOfPartT, Option.some_inj] at h; subst h
    simp only [evalExpr, Option.bind_eq_bind] at he
    cases hp : evalExpr we env p with
    | none => rw [hp] at he; simp at he
    | some x =>
      rw [hp] at he; simp only [Option.bind_some, Option.some_inj] at he
      subst he; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | .op .., _, h, _, _ => by simp [widthOfPartT] at h
  | .concat .., _, h, _, _ => by simp [widthOfPartT] at h
  | .sliceDim .., _, h, _, _ => by simp [widthOfPartT] at h
  | .index .., _, h, _, _ => by simp [widthOfPartT] at h

theorem mapM_widthOfPartT (we : WEnv) (wt : Std.HashMap String Nat)
    (hwt : ∀ n w, wt.get? n = some w → we n = w) :
    ∀ (ps : List Expr) (ws : List Nat),
      ps.mapM (widthOfPartT wt) = some ws →
      ws = ps.map (widthOf we)
        ∧ ∀ p ∈ ps, ∃ w, widthOfPartT wt p = some w
  | [], ws, h => by simp [List.mapM_nil] at h; simp [← h]
  | p :: ps', ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hp : widthOfPartT wt p with
    | none => rw [hp] at h; simp at h
    | some w =>
      rw [hp] at h
      cases hr : ps'.mapM (widthOfPartT wt) with
      | none => rw [hr] at h; simp at h
      | some ws' =>
        rw [hr] at h; simp only [Option.bind_some, Option.pure_def,
          Option.some_inj] at h
        obtain ⟨ih1, ih2⟩ := mapM_widthOfPartT we wt hwt ps' ws' hr
        subst h
        refine ⟨by simp [ih1, widthOfPartT_width we wt hwt p w hp], ?_⟩
        intro q hq
        cases hq with
        | head => exact ⟨w, hp⟩
        | tail _ hq => exact ih2 q hq

theorem foldl_add_go (we : WEnv) :
    ∀ (ps : List Expr) (acc : Nat),
      ((ps.map (widthOf we)).foldl (· + ·) acc) = acc + widthOf.go we ps
  | [], acc => by simp [widthOf.go]
  | p :: ps', acc => by
    simp only [List.map_cons, List.foldl_cons, foldl_add_go we ps',
      widthOf.go]
    omega

mutual
theorem flattenE_width (we : WEnv) : ∀ (e : Expr),
    widthOf.go we (flattenE e) = widthOf we e
  | .concat ps => by
    simp only [flattenE, widthOf]
    exact flattenL_width we ps
  | .const .. => by simp [flattenE, widthOf.go]
  | .ref .. => by simp [flattenE, widthOf.go]
  | .op .. => by simp [flattenE, widthOf.go]
  | .slice .. => by simp [flattenE, widthOf.go]
  | .sliceDim .. => by simp [flattenE, widthOf.go]
  | .index .. => by simp [flattenE, widthOf.go]

theorem flattenL_width (we : WEnv) : ∀ (l : List Expr),
    widthOf.go we (flattenL l) = widthOf.go we l
  | [] => by simp [flattenL]
  | a :: rest => by
    simp only [flattenL, widthgo_append we, widthOf.go,
      flattenE_width we a, flattenL_width we rest]
end

mutual
theorem flattenE_eval (we : WEnv) (env : Env) :
    ∀ (e : Expr) (u : Nat), evalExpr we env e = some u →
    ∃ vs, evalList we env (flattenE e) = some vs ∧
      evalExpr.go we (flattenE e) vs = mask (widthOf we e) u
  | .concat ps, u, h => by
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hL : evalList we env ps with
    | none => rw [hL] at h; simp at h
    | some vals =>
      rw [hL] at h; simp only [Option.bind_some, Option.some_inj] at h
      obtain ⟨vs, hvs, hgo⟩ := flattenL_eval we env ps vals hL
      refine ⟨vs, by simpa [flattenE] using hvs, ?_⟩
      have hlt : evalExpr.go we ps vals < 2 ^ widthOf.go we ps :=
        go_lt we ps vals (evalList_len hL).symm
      simp only [flattenE, widthOf, hgo, ← h, mask,
        Nat.mod_eq_of_lt hlt]
  | .const v w, u, h =>
    ⟨[u], by simp [flattenE, evalList, h],
      by simp [flattenE, evalExpr.go]⟩
  | .ref n, u, h =>
    ⟨[u], by simp [flattenE, evalList, h],
      by simp [flattenE, evalExpr.go]⟩
  | .op .., u, h =>
    ⟨[u], by simp [flattenE, evalList, h],
      by simp [flattenE, evalExpr.go]⟩
  | .slice .., u, h =>
    ⟨[u], by simp [flattenE, evalList, h],
      by simp [flattenE, evalExpr.go]⟩
  | .sliceDim .., u, h => by simp [evalExpr] at h
  | .index .., u, h => by simp [evalExpr] at h

theorem flattenL_eval (we : WEnv) (env : Env) :
    ∀ (l : List Expr) (vals : List Nat), evalList we env l = some vals →
    ∃ vs, evalList we env (flattenL l) = some vs ∧
      evalExpr.go we (flattenL l) vs = evalExpr.go we l vals
  | [], vals, h => by
    simp only [evalList, Option.some_inj] at h
    subst h
    exact ⟨[], by simp [flattenL, evalList], by simp [flattenL]⟩
  | a :: rest, vals, h => by
    simp only [evalList, Option.bind_eq_bind] at h
    cases hA : evalExpr we env a with
    | none => rw [hA] at h; simp at h
    | some u =>
      rw [hA] at h
      cases hR : evalList we env rest with
      | none => rw [hR] at h; simp at h
      | some vrest =>
        rw [hR] at h; simp only [Option.bind_some, Option.some_inj] at h
        subst h
        obtain ⟨va, hva, hgoa⟩ := flattenE_eval we env a u hA
        obtain ⟨vb, hvb, hgob⟩ := flattenL_eval we env rest vrest hR
        refine ⟨va ++ vb, by
          simp only [flattenL]
          exact evalList_append hva hvb, ?_⟩
        have hlena : va.length = (flattenE a).length :=
          evalList_len hva
        have hlenb : vb.length = (flattenL rest).length :=
          evalList_len hvb
        have hlenr : rest.length = vrest.length :=
          (evalList_len hR).symm
        simp only [flattenL]
        rw [go_append we _ _ va vb hlena hlenb, hgoa, hgob,
          flattenL_width we rest]
        simp only [evalExpr.go]
        rw [zipFold_width we rest vrest (by omega)]
        simp
end

theorem findWindow_lt (we : WEnv) (hi lo : Nat) :
    ∀ (ps : List Expr) (acc : Nat), acc = widthOf.go we ps →
    ∀ r, findWindow hi lo ps (ps.map (widthOf we)) acc = some r →
      hi < acc ∧ lo ≤ hi
  | [], acc, hacc, r, h => by simp [findWindow] at h
  | p :: ps', acc, hacc, r, h => by
    simp only [widthOf.go] at hacc
    simp only [List.map_cons, findWindow] at h
    split at h
    · rename_i hc; omega
    · split at h
      · rename_i hc; omega
      · have := findWindow_lt we hi lo ps' (acc - widthOf we p)
          (by omega) r h
        omega

theorem findWindow_width (we : WEnv) (hi lo : Nat) :
    ∀ (ps : List Expr) (acc : Nat), acc = widthOf.go we ps →
    ∀ r, findWindow hi lo ps (ps.map (widthOf we)) acc = some r →
      widthOf we r = hi - lo + 1
  | [], acc, hacc, r, h => by simp [findWindow] at h
  | p :: ps', acc, hacc, r, h => by
    simp only [widthOf.go] at hacc
    simp only [List.map_cons, findWindow] at h
    split at h
    · rename_i hc
      cases h
      omega
    · split at h
      · rename_i hc
        cases h
        simp only [widthOf]
        omega
      · exact findWindow_width we hi lo ps' (acc - widthOf we p)
          (by omega) r h

/- ---- width preservation ---- -/

theorem widthOf_op_shape (we : WEnv) {args args' : List Expr} (o : Operator)
    (hm : WidthMatch we args args') :
    widthOf we (.op o args') = widthOf we (.op o args) := by
  cases o <;>
    (cases hm with
     | nil => rfl
     | cons h1 hrest =>
       cases hrest with
       | nil => simp [widthOf, h1]
       | cons h2 hrest2 =>
         cases hrest2 with
         | nil => simp [widthOf, h1, h2]
         | cons h3 hrest3 =>
           cases hrest3 with
           | nil => simp [widthOf, h1, h2, h3]
           | cons h4 hrest4 => simp [widthOf, h1, h2, h3])

/-- Slice resolution preserves `widthOf` (under a width table that
    agrees with the semantic width environment). -/
theorem resolveSlicesT_width (wt : Std.HashMap String Nat) (we : WEnv)
    (hwt : ∀ n w, wt.get? n = some w → we n = w) :
    ∀ fuel e, widthOf we (resolveSlicesT wt fuel e) = widthOf we e := by
  intro fuel e
  induction fuel, e using resolveSlicesT.induct wt
    (motive2 := fun fuel args =>
      WidthMatch we args (resolveSlicesTL wt fuel args)) with
  | case1 e => rw [rsT_zero]
  | case2 fuel parts0 hi lo parts hmap ih =>
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap
    rw [rsT_slice_concat, hmap]
    simp [widthOf]
  | case3 fuel parts0 hi lo parts ws hmap r hfw ih =>
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap hfw
    obtain ⟨hws, _⟩ := mapM_widthOfPartT we wt hwt _ _ hmap
    subst hws
    rw [foldl_add_go we _ 0] at hfw
    have hwr := findWindow_width we hi lo _ _ (by omega) r hfw
    rw [rsT_slice_concat, hmap]
    dsimp only
    rw [foldl_add_go we _ 0, hfw]
    simp [widthOf, hwr]
  | case4 fuel parts0 hi lo parts ws hmap hfw ih =>
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap hfw
    rw [rsT_slice_concat, hmap]
    dsimp only
    rw [hfw]
    simp [widthOf]
  | case5 fuel o args ih =>
    rw [rsT_op]
    exact widthOf_op_shape we o ih
  | case6 fuel args ih =>
    rw [rsT_concat]
    simp [widthOf, widthOfGo_congr we ih]
  | case7 fuel e hi lo hne parts hcp ih2 ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), hcp]
    dsimp only
    rw [ih1]
    simp [widthOf]
  | case8 fuel e hi lo hne n href hguard ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), href]
    dsimp only
    rw [if_pos hguard]
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    obtain ⟨hlo0, hwn⟩ := hguard
    subst hlo0
    simp [widthOf, hwt n (hi + 1) hwn]
  | case9 fuel e hi lo hne n href hguard ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), href]
    dsimp only
    rw [if_neg hguard]
    simp [widthOf]
  | case10 fuel e hi lo hne inner ihi ilo hsl hguard ih2 ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), hsl]
    dsimp only
    rw [if_pos hguard, ih1]
    simp only [widthOf]
    omega
  | case11 fuel e hi lo hne inner ihi ilo hsl hguard ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), hsl]
    dsimp only
    rw [if_neg hguard]
    simp [widthOf]
  | case12 fuel e hi lo hne hnc hnr hns ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h)]
    cases hre : resolveSlicesT wt fuel e with
    | concat parts => exact (hnc parts hre).elim
    | ref n => exact (hnr n hre).elim
    | slice i a b => exact (hns i a b hre).elim
    | const v w => simp [widthOf]
    | op o args => simp [widthOf]
    | sliceDim i d j => simp [widthOf]
    | index a i => simp [widthOf]
  | case13 x e h0 h1 h2 h3 h4 =>
    match x, h0 with
    | fuel + 1, _ =>
      cases e with
      | op o args => exact (h2 fuel o args rfl rfl).elim
      | concat args => exact (h3 fuel args rfl rfl).elim
      | slice s a b => exact (h4 fuel s a b rfl rfl).elim
      | const v w => rw [rsT_const]
      | ref n => rw [rsT_ref]
      | sliceDim i d j => rw [rsT_sliceDim]
      | index a i => rw [rsT_index]
  | case14 fuel =>
    rw [rsTL_nil]
    exact .nil
  | case15 fuel a rest ih2 ih1 =>
    rw [rsTL_cons]
    exact .cons ih2 ih1

/-- Standalone list form (`WidthMatch` against the resolved list). -/
theorem resolveSlicesTL_width (wt : Std.HashMap String Nat) (we : WEnv)
    (hwt : ∀ n w, wt.get? n = some w → we n = w) :
    ∀ fuel args, WidthMatch we args (resolveSlicesTL wt fuel args)
  | _, [] => by rw [rsTL_nil]; exact .nil
  | fuel, a :: rest => by
    rw [rsTL_cons]
    exact .cons (resolveSlicesT_width wt we hwt fuel a)
      (resolveSlicesTL_width wt we hwt fuel rest)

/- ---- window extraction: the semantic core ---- -/

/-- A successful window search returns exactly the sliced-out bits of
    the MSB-first assembly.  `acc` must be the total width; parts must
    be width-masked (`hmask` — const/slice mask themselves, refs need
    the bounded environment). -/
theorem findWindow_eval (we : WEnv) (env : Env) (hi lo : Nat) :
    ∀ (ps : List Expr) (vals : List Nat) (acc : Nat),
      acc = widthOf.go we ps →
      evalList we env ps = some vals →
      (∀ p ∈ ps, ∀ u, evalExpr we env p = some u → u < 2 ^ widthOf we p) →
      ∀ r, findWindow hi lo ps (ps.map (widthOf we)) acc = some r →
        evalExpr we env r
          = some (mask (hi - lo + 1) (evalExpr.go we ps vals >>> lo))
  | [], _, acc, _, _, _, r, h => by simp [findWindow] at h
  | p :: ps', vals, acc, hacc, hvals, hmask, r, h => by
    simp only [evalList, Option.bind_eq_bind] at hvals
    cases hP : evalExpr we env p with
    | none => rw [hP] at hvals; simp at hvals
    | some v =>
      rw [hP] at hvals
      cases hR : evalList we env ps' with
      | none => rw [hR] at hvals; simp at hvals
      | some vs =>
        rw [hR] at hvals
        simp only [Option.bind_some, Option.some_inj] at hvals
        subst hvals
        simp only [widthOf.go] at hacc
        have hlen : ps'.length ≤ vs.length := by
          have := evalList_len hR; omega
        have hv : v < 2 ^ widthOf we p := hmask p (by simp) v hP
        have hmv : mask (widthOf we p) v = v := Nat.mod_eq_of_lt hv
        have hgoR : evalExpr.go we ps' vs < 2 ^ widthOf.go we ps' :=
          go_lt we ps' vs (by have := evalList_len hR; omega)
        have hgo : evalExpr.go we (p :: ps') (v :: vs)
            = v <<< widthOf.go we ps' ||| evalExpr.go we ps' vs := by
          simp only [evalExpr.go]
          rw [zipFold_width we ps' vs hlen]
          simp only [Nat.zero_add, hmv]
        simp only [List.map_cons, findWindow] at h
        split at h
        · -- exact window on the head part
          rename_i hc
          cases h
          rw [hP]
          have hwid : hi - lo + 1 = widthOf we p := by omega
          have hlo : lo = widthOf.go we ps' := by omega
          have hshift : (v <<< widthOf.go we ps' ||| evalExpr.go we ps' vs)
              >>> widthOf.go we ps' = v := by
            rw [Nat.shiftRight_eq_div_pow, Nat.or_div_two_pow,
                Nat.shiftLeft_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
                Nat.div_eq_of_lt hgoR, Nat.or_zero]
          rw [hgo, hwid, hlo, hshift, hmv]
        · split at h
          · -- window contained in the head part
            rename_i hc
            cases h
            have hRw : acc - widthOf we p = widthOf.go we ps' := by omega
            rw [hRw]
            simp only [evalExpr, Option.bind_eq_bind, hP, Option.bind_some]
            congr 1
            have hww : hi - widthOf.go we ps' - (lo - widthOf.go we ps') + 1
                = hi - lo + 1 := by omega
            rw [hww, hgo]
            have hR_le_lo : widthOf.go we ps' ≤ lo := by omega
            have hsplit : (v <<< widthOf.go we ps'
                  ||| evalExpr.go we ps' vs) >>> lo
                = v >>> (lo - widthOf.go we ps') := by
              rw [Nat.shiftRight_eq_div_pow, Nat.or_div_two_pow]
              have hgoR0 : evalExpr.go we ps' vs / 2 ^ lo = 0 :=
                Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hgoR
                  (Nat.pow_le_pow_right (by omega) hR_le_lo))
              rw [hgoR0, Nat.or_zero, Nat.shiftLeft_eq]
              have h2lo : (2 : Nat) ^ lo
                  = 2 ^ widthOf.go we ps'
                    * 2 ^ (lo - widthOf.go we ps') := by
                rw [← Nat.pow_add]; congr 1; omega
              rw [h2lo, ← Nat.div_div_eq_div_mul,
                  Nat.mul_div_cancel _ (Nat.two_pow_pos _),
                  Nat.shiftRight_eq_div_pow]
            rw [hsplit]
          · -- window inside the tail
            have hRw : acc - widthOf we p = widthOf.go we ps' := by omega
            rw [hRw] at h
            have hmask' : ∀ q ∈ ps', ∀ u, evalExpr we env q = some u →
                u < 2 ^ widthOf we q := fun q hq => hmask q (by simp [hq])
            obtain ⟨hlt, hlohi⟩ := findWindow_lt we hi lo ps' _ rfl r h
            have ih := findWindow_eval we env hi lo ps' vs _ rfl hR hmask' r h
            rw [ih, hgo]
            have hsp : v * 2 ^ widthOf.go we ps' / 2 ^ lo
                = v * 2 ^ (widthOf.go we ps' - lo) := by
              have h2R : (2 : Nat) ^ widthOf.go we ps'
                  = 2 ^ lo * 2 ^ (widthOf.go we ps' - lo) := by
                rw [← Nat.pow_add]; congr 1; omega
              calc v * 2 ^ widthOf.go we ps' / 2 ^ lo
                  = v * (2 ^ lo * 2 ^ (widthOf.go we ps' - lo)) / 2 ^ lo := by
                    rw [← h2R]
                _ = v * 2 ^ (widthOf.go we ps' - lo) * 2 ^ lo / 2 ^ lo := by
                    rw [Nat.mul_comm (2 ^ lo) _, ← Nat.mul_assoc]
                _ = v * 2 ^ (widthOf.go we ps' - lo) :=
                    Nat.mul_div_cancel _ (Nat.two_pow_pos _)
            have hz : v * 2 ^ (widthOf.go we ps' - lo)
                % 2 ^ (hi - lo + 1) = 0 := by
              have h2s : (2 : Nat) ^ (widthOf.go we ps' - lo)
                  = 2 ^ (hi - lo + 1)
                    * 2 ^ (widthOf.go we ps' - lo - (hi - lo + 1)) := by
                rw [← Nat.pow_add]; congr 1; omega
              calc v * 2 ^ (widthOf.go we ps' - lo) % 2 ^ (hi - lo + 1)
                  = v * (2 ^ (hi - lo + 1)
                      * 2 ^ (widthOf.go we ps' - lo - (hi - lo + 1)))
                      % 2 ^ (hi - lo + 1) := by rw [← h2s]
                _ = v * 2 ^ (widthOf.go we ps' - lo - (hi - lo + 1))
                      * 2 ^ (hi - lo + 1) % 2 ^ (hi - lo + 1) := by
                    rw [Nat.mul_comm (2 ^ (hi - lo + 1)) _, ← Nat.mul_assoc]
                _ = 0 := Nat.mul_mod_left _ _
            have hkey : mask (hi - lo + 1)
                ((v <<< widthOf.go we ps' ||| evalExpr.go we ps' vs) >>> lo)
                = mask (hi - lo + 1) (evalExpr.go we ps' vs >>> lo) := by
              simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mask]
              rw [Nat.or_div_two_pow, Nat.or_mod_two_pow, hsp, hz,
                  Nat.zero_or]
            rw [hkey]

/-- Uniform slice decomposition: the outer slice equation with the
    operand's evaluation plugged in (avoids `simp only [evalExpr]`
    over-unfolding a concrete-constructor operand). -/
theorem eval_slice_of (we : WEnv) (env : Env) (X : Expr) (hi lo u : Nat)
    (hX : evalExpr we env X = some u) :
    evalExpr we env (.slice X hi lo)
      = some (mask (hi - lo + 1) (u >>> lo)) := by
  simp only [evalExpr, Option.bind_eq_bind]
  rw [hX]
  simp

/- ---- eval preservation: slice resolution is sound ---- -/

/-- THE SLICE-RESOLUTION THEOREM: under a width table that agrees with
    the width environment and a bounded environment (both supplied by
    the arcs' machinery), the resolved expression evaluates to exactly
    the original's value. -/
theorem resolveSlicesT_eval (wt : Std.HashMap String Nat) (we : WEnv)
    (env : Env)
    (hwt : ∀ n w, wt.get? n = some w → we n = w)
    (hb : ∀ n, env n < 2 ^ we n) :
    ∀ fuel e, ∀ v, evalExpr we env e = some v →
      evalExpr we env (resolveSlicesT wt fuel e) = some v := by
  intro fuel e
  induction fuel, e using resolveSlicesT.induct wt
    (motive2 := fun fuel args => ∀ vs,
      evalList we env args = some vs →
      evalList we env (resolveSlicesTL wt fuel args) = some vs) with
  | case1 e =>
    intro v h
    rw [rsT_zero]
    exact h
  | case2 fuel parts0 hi lo parts hmap ih =>
    intro v h
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap
    rw [rsT_slice_concat, hmap]
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hL : evalList we env parts0 with
    | none => rw [hL] at h; simp at h
    | some vals0 =>
      rw [hL] at h
      simp only [Option.bind_some, Option.some_inj] at h
      obtain ⟨vals1, hfl, hflgo⟩ := flattenL_eval we env parts0 vals0 hL
      have hTL := ih vals1 hfl
      have hwm := resolveSlicesTL_width wt we hwt fuel (flattenL parts0)
      simp only [evalExpr, Option.bind_eq_bind, hTL, Option.bind_some,
        Option.some_inj]
      rw [evalGo_congr we hwm vals1, hflgo, h]
  | case3 fuel parts0 hi lo parts ws hmap r hfw ih =>
    intro v h
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap hfw
    obtain ⟨hws, hsome⟩ := mapM_widthOfPartT we wt hwt _ _ hmap
    subst hws
    rw [foldl_add_go we _ 0] at hfw
    rw [rsT_slice_concat, hmap]
    dsimp only
    rw [foldl_add_go we _ 0, hfw]
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hL : evalList we env parts0 with
    | none => rw [hL] at h; simp at h
    | some vals0 =>
      rw [hL] at h
      simp only [Option.bind_some, Option.some_inj] at h
      obtain ⟨vals1, hfl, hflgo⟩ := flattenL_eval we env parts0 vals0 hL
      have hTL := ih vals1 hfl
      have hwm := resolveSlicesTL_width wt we hwt fuel (flattenL parts0)
      have hmaskP : ∀ p ∈ resolveSlicesTL wt fuel (flattenL parts0),
          ∀ u, evalExpr we env p = some u → u < 2 ^ widthOf we p := by
        intro p hp u hu
        obtain ⟨w, hw⟩ := hsome p hp
        have := widthOfPartT_masked we env wt hwt hb p w hw u hu
        rwa [widthOfPartT_width we wt hwt p w hw]
      have hfe := findWindow_eval we env hi lo _ vals1 _ (by omega) hTL
        hmaskP r hfw
      rw [hfe, evalGo_congr we hwm vals1, hflgo, h]
  | case4 fuel parts0 hi lo parts ws hmap hfw ih =>
    intro v h
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap hfw
    rw [rsT_slice_concat, hmap]
    dsimp only
    rw [hfw]
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hL : evalList we env parts0 with
    | none => rw [hL] at h; simp at h
    | some vals0 =>
      rw [hL] at h
      simp only [Option.bind_some, Option.some_inj] at h
      obtain ⟨vals1, hfl, hflgo⟩ := flattenL_eval we env parts0 vals0 hL
      have hTL := ih vals1 hfl
      have hwm := resolveSlicesTL_width wt we hwt fuel (flattenL parts0)
      simp only [evalExpr, Option.bind_eq_bind, hTL, Option.bind_some,
        Option.some_inj]
      rw [evalGo_congr we hwm vals1, hflgo, h]
  | case5 fuel o args ih =>
    intro v h
    rw [rsT_op]
    simp only [evalExpr, Option.bind_eq_bind] at h ⊢
    cases hL : evalList we env args with
    | none => rw [hL] at h; simp at h
    | some vals =>
      rw [hL] at h
      simp only [Option.bind_some] at h
      rw [ih vals hL]
      simp only [Option.bind_some]
      rw [widthOf_op_shape we o (resolveSlicesTL_width wt we hwt fuel args),
          evalOp_congr we (resolveSlicesTL_width wt we hwt fuel args) o
            vals _]
      exact h
  | case6 fuel args ih =>
    intro v h
    rw [rsT_concat]
    simp only [evalExpr, Option.bind_eq_bind] at h ⊢
    cases hL : evalList we env args with
    | none => rw [hL] at h; simp at h
    | some vals =>
      rw [hL] at h
      simp only [Option.bind_some] at h
      rw [ih vals hL]
      simp only [Option.bind_some]
      rw [evalGo_congr we (resolveSlicesTL_width wt we hwt fuel args) vals]
      exact h
  | case7 fuel e hi lo hne parts hcp ih2 ih1 =>
    intro v h
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps hh => hne ps hh), hcp]
    dsimp only
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hE : evalExpr we env e with
    | none => rw [hE] at h; simp at h
    | some u =>
      rw [hE] at h
      simp only [Option.bind_some, Option.some_inj] at h
      have hE' : evalExpr we env (.concat parts) = some u := by
        rw [← hcp]; exact ih2 u hE
      apply ih1
      rw [eval_slice_of we env _ hi lo u hE', h]
  | case8 fuel e hi lo hne n href hguard ih1 =>
    intro v h
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps hh => hne ps hh), href]
    dsimp only
    rw [if_pos hguard]
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    obtain ⟨hlo0, hwn⟩ := hguard
    subst hlo0
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hE : evalExpr we env e with
    | none => rw [hE] at h; simp at h
    | some u =>
      rw [hE] at h
      simp only [Option.bind_some, Option.some_inj] at h
      have hEn := ih1 u hE
      rw [href] at hEn
      simp only [evalExpr, Option.some_inj] at hEn
      simp only [evalExpr, Option.some_inj]
      rw [← h, ← hEn]
      have hwn' : we n = hi + 1 := hwt n (hi + 1) hwn
      have hlt : env n < 2 ^ (hi + 1) := by rw [← hwn']; exact hb n
      simp [mask, Nat.shiftRight_zero, Nat.mod_eq_of_lt hlt]
  | case9 fuel e hi lo hne n href hguard ih1 =>
    intro v h
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps hh => hne ps hh), href]
    dsimp only
    rw [if_neg hguard]
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hE : evalExpr we env e with
    | none => rw [hE] at h; simp at h
    | some u =>
      rw [hE] at h
      simp only [Option.bind_some, Option.some_inj] at h
      have hEn := ih1 u hE
      rw [href] at hEn
      rw [eval_slice_of we env _ hi lo u hEn, h]
  | case10 fuel e hi lo hne inner ihi ilo hsl hguard ih2 ih1 =>
    intro v h
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps hh => hne ps hh), hsl]
    dsimp only
    rw [if_pos hguard]
    obtain ⟨hcont, hlohi⟩ := hguard
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hE : evalExpr we env e with
    | none => rw [hE] at h; simp at h
    | some u =>
      rw [hE] at h
      simp only [Option.bind_some, Option.some_inj] at h
      have hEs := ih2 u hE
      rw [hsl] at hEs
      simp only [evalExpr, Option.bind_eq_bind] at hEs
      cases hI : evalExpr we env inner with
      | none => rw [hI] at hEs; simp at hEs
      | some x =>
        rw [hI] at hEs
        simp only [Option.bind_some, Option.some_inj] at hEs
        apply ih1
        rw [eval_slice_of we env inner (ilo + hi) (ilo + lo) x hI]
        simp only [Option.some_inj]
        rw [← h, ← hEs]
        have hww : ilo + hi - (ilo + lo) + 1 = hi - lo + 1 := by omega
        rw [hww]
        simp only [Nat.shiftRight_eq_div_pow, mask]
        have hA : (2 : Nat) ^ (ihi - ilo + 1)
            = 2 ^ lo * 2 ^ (ihi - ilo + 1 - lo) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hdd : x / 2 ^ ilo / 2 ^ lo = x / 2 ^ (ilo + lo) := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        rw [hA, Nat.mod_mul_right_div_self, hdd,
            Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  | case11 fuel e hi lo hne inner ihi ilo hsl hguard ih1 =>
    intro v h
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps hh => hne ps hh), hsl]
    dsimp only
    rw [if_neg hguard]
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hE : evalExpr we env e with
    | none => rw [hE] at h; simp at h
    | some u =>
      rw [hE] at h
      simp only [Option.bind_some, Option.some_inj] at h
      have hEs := ih1 u hE
      rw [hsl] at hEs
      rw [eval_slice_of we env _ hi lo u hEs, h]
  | case12 fuel e hi lo hne hnc hnr hns ih1 =>
    intro v h
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps hh => hne ps hh)]
    simp only [evalExpr, Option.bind_eq_bind] at h
    cases hE : evalExpr we env e with
    | none => rw [hE] at h; simp at h
    | some u =>
      rw [hE] at h
      simp only [Option.bind_some, Option.some_inj] at h
      have hEr := ih1 u hE
      cases hre : resolveSlicesT wt fuel e with
      | concat parts => exact (hnc parts hre).elim
      | ref n => exact (hnr n hre).elim
      | slice i a b => exact (hns i a b hre).elim
      | const cv cw =>
        rw [hre] at hEr
        rw [eval_slice_of we env _ hi lo u hEr, h]
      | op o args =>
        rw [hre] at hEr
        rw [eval_slice_of we env _ hi lo u hEr, h]
      | sliceDim i d j =>
        rw [hre] at hEr
        simp [evalExpr] at hEr
      | index a i =>
        rw [hre] at hEr
        simp [evalExpr] at hEr
  | case13 x e h0 h1 h2 h3 h4 =>
    intro v h
    match x, h0 with
    | fuel + 1, _ =>
      cases e with
      | op o args => exact (h2 fuel o args rfl rfl).elim
      | concat args => exact (h3 fuel args rfl rfl).elim
      | slice s a b => exact (h4 fuel s a b rfl rfl).elim
      | const cv cw => rw [rsT_const]; exact h
      | ref n => rw [rsT_ref]; exact h
      | sliceDim i d j => rw [rsT_sliceDim]; exact h
      | index a i => rw [rsT_index]; exact h
  | case14 fuel vs hvs =>
    rw [rsTL_nil]
    exact hvs
  | case15 fuel a rest ih2 ih1 vs hvs =>
    rw [rsTL_cons]
    simp only [evalList, Option.bind_eq_bind] at hvs ⊢
    cases hA : evalExpr we env a with
    | none => rw [hA] at hvs; simp at hvs
    | some u =>
      rw [hA] at hvs
      cases hR : evalList we env rest with
      | none => rw [hR] at hvs; simp at hvs
      | some urest =>
        rw [hR] at hvs
        rw [ih2 u hA, ih1 urest hR]
        exact hvs

/- ---- the composed capstone ---- -/

open Sparkle.IR.Optimize (buildDefMap) in
/-- THE SEAM, fully composed: on a well-ordered, memory-free,
    self-loop-free body whose assignments respect the declared widths
    (`hwf`), with a width table agreeing with the width environment
    (`hwt`) and the fold's final environment bounded (`hb` — supplied
    by Arc 2's bounded-env machinery), the INLINED-and-SLICE-RESOLVED
    cone — the exact expression `#verify_elab` / `#verify_elab_deep`'s
    goal generator manipulates — evaluates, in the fold's final
    environment, to the original expression's value. -/
theorem cone_resolved_agrees_with_fold (we : WEnv) (mems : MEnv)
    {done : List String} {body : List Stmt} {env0 env1 : Env}
    (stopAt : Std.HashMap String Bool) (wt : Std.HashMap String Nat)
    (hWO : Sparkle.IR.Reorder.WO done body)
    (hm : memFree body) (hsr : noSelfRead body)
    (hrun : evalAssigns we mems body env0 = some env1)
    (hwf : ∀ n rhs, (buildDefMap body).get? n = some rhs →
      stopAt.contains n = false → widthOf we rhs = we n)
    (hwt : ∀ n w, wt.get? n = some w → we n = w)
    (hb : ∀ n, env1 n < 2 ^ we n)
    {fuel : Nat} {e e' : Expr}
    (hinl : inlineConeT (buildDefMap body) stopAt fuel e = .ok e')
    (rfuel : Nat) {v : Nat} (hv : evalExpr we env1 e = some v) :
    evalExpr we env1 (resolveSlicesT wt rfuel e') = some v := by
  apply resolveSlicesT_eval wt we env1 hwt hb
  rw [cone_agrees_with_fold we mems stopAt hWO hm hsr hrun hwf hinl]
  exact hv

end ResolveSlices

/- ------------------------------------------------------------------ -/
/- The bridge to the generated recurrence.

   `#verify_elab`'s generated `irTrace` evaluates each register's cone
   in the SEED environment (registers ↦ trace components, inputs ↦
   signal samples) — not in the fold's final environment.  The two
   agree because a fully-inlined cone only reads stop-set names
   (`inlineConeT_refs`, `resolveSlicesT_refs`) and the combinational
   fold never writes those (`evalAssigns_frame`).

   The decidable checkers at the end make every hypothesis of the
   composed capstone per-instance dischargeable: `woCheck` (existing,
   ReorderInvariance) + `memFreeCheck` + `noSelfReadCheck` +
   `hwfCheck` + `stopAtFrozenCheck`. -/
section Bridge

-- `inlineConeT … = .ok cone` facts are discharged per instance by
-- `native_decide`; the equality needs a Decidable instance on Except.
deriving instance DecidableEq for Except

open Sparkle.IR.Reorder
open Sparkle.IR.Optimize (buildDefMap DefMap)

/- ---- reference sets ---- -/

theorem refsList_append :
    ∀ (xs ys : List Expr),
      refsOf.refsList (xs ++ ys) = refsOf.refsList xs ++ refsOf.refsList ys
  | [], ys => by simp [refsOf.refsList]
  | x :: xs', ys => by
    simp [refsOf.refsList, refsList_append xs' ys]

mutual
theorem flattenE_refs (e : Expr) :
    refsOf.refsList (flattenE e) = refsOf e := by
  cases e with
  | concat ps =>
    simp only [flattenE, refsOf]
    exact flattenL_refs ps
  | const v w => simp [flattenE, refsOf.refsList]
  | ref n => simp [flattenE, refsOf.refsList]
  | op o args => simp [flattenE, refsOf.refsList]
  | slice i a b => simp [flattenE, refsOf.refsList]
  | sliceDim i d j => simp [flattenE, refsOf.refsList]
  | index a i => simp [flattenE, refsOf.refsList]

theorem flattenL_refs (l : List Expr) :
    refsOf.refsList (flattenL l) = refsOf.refsList l := by
  cases l with
  | nil => simp [flattenL]
  | cons a rest =>
    simp only [flattenL, refsList_append, refsOf.refsList,
      flattenE_refs a, flattenL_refs rest]
end

theorem findWindow_refs (hi lo : Nat) :
    ∀ (ps : List Expr) (ws : List Nat) (acc : Nat) (r : Expr),
      findWindow hi lo ps ws acc = some r →
      ∀ n ∈ refsOf r, n ∈ refsOf.refsList ps
  | [], ws, acc, r, h => by
    cases ws <;> simp [findWindow] at h
  | p :: ps', [], acc, r, h => by simp [findWindow] at h
  | p :: ps', w :: ws', acc, r, h => by
    simp only [findWindow] at h
    split at h
    · cases h
      intro n hn
      simp [refsOf.refsList, hn]
    · split at h
      · cases h
        intro n hn
        simp only [refsOf] at hn
        simp [refsOf.refsList, hn]
      · intro n hn
        have := findWindow_refs hi lo ps' ws' (acc - w) r h n hn
        simp [refsOf.refsList, this]

/-- Slice resolution never introduces a reference. -/
theorem resolveSlicesT_refs (wt : Std.HashMap String Nat) :
    ∀ fuel e, ∀ n ∈ refsOf (resolveSlicesT wt fuel e), n ∈ refsOf e := by
  intro fuel e
  induction fuel, e using resolveSlicesT.induct wt
    (motive2 := fun fuel args =>
      ∀ n ∈ refsOf.refsList (resolveSlicesTL wt fuel args),
        n ∈ refsOf.refsList args) with
  | case1 e =>
    rw [rsT_zero]
    exact fun n hn => hn
  | case2 fuel parts0 hi lo parts hmap ih =>
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap
    rw [rsT_slice_concat, hmap]
    intro n hn
    simp only [refsOf] at hn ⊢
    rw [← flattenL_refs parts0]
    exact ih n hn
  | case3 fuel parts0 hi lo parts ws hmap r hfw ih =>
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap hfw
    rw [rsT_slice_concat, hmap]
    dsimp only
    rw [hfw]
    intro n hn
    simp only [refsOf]
    rw [← flattenL_refs parts0]
    exact ih n (findWindow_refs hi lo _ _ _ r hfw n hn)
  | case4 fuel parts0 hi lo parts ws hmap hfw ih =>
    rw [show parts = resolveSlicesTL wt fuel (flattenL parts0) from rfl]
      at hmap hfw
    rw [rsT_slice_concat, hmap]
    dsimp only
    rw [hfw]
    intro n hn
    simp only [refsOf] at hn ⊢
    rw [← flattenL_refs parts0]
    exact ih n hn
  | case5 fuel o args ih =>
    rw [rsT_op]
    intro n hn
    simp only [refsOf] at hn ⊢
    exact ih n hn
  | case6 fuel args ih =>
    rw [rsT_concat]
    intro n hn
    simp only [refsOf] at hn ⊢
    exact ih n hn
  | case7 fuel e hi lo hne parts hcp ih2 ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), hcp]
    dsimp only
    intro n hn
    have h1 := ih1 n hn
    simp only [refsOf] at h1 ⊢
    have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
      rw [hcp]; simpa [refsOf] using h1
    exact ih2 n h2
  | case8 fuel e hi lo hne n' href hguard ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), href]
    dsimp only
    rw [if_pos hguard]
    intro n hn
    have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
      rw [href]; exact hn
    simpa [refsOf] using ih1 n h2
  | case9 fuel e hi lo hne n' href hguard ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), href]
    dsimp only
    rw [if_neg hguard]
    intro n hn
    simp only [refsOf] at hn ⊢
    have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
      rw [href]; exact hn
    exact ih1 n h2
  | case10 fuel e hi lo hne inner ihi ilo hsl hguard ih2 ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), hsl]
    dsimp only
    rw [if_pos hguard]
    intro n hn
    have h1 := ih1 n hn
    simp only [refsOf] at h1 ⊢
    have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
      rw [hsl]; simpa [refsOf] using h1
    exact ih2 n h2
  | case11 fuel e hi lo hne inner ihi ilo hsl hguard ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h), hsl]
    dsimp only
    rw [if_neg hguard]
    intro n hn
    simp only [refsOf] at hn ⊢
    have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
      rw [hsl]; simpa [refsOf] using hn
    exact ih1 n h2
  | case12 fuel e hi lo hne hnc hnr hns ih1 =>
    rw [rsT_slice_reduce wt fuel e hi lo (fun ps h => hne ps h)]
    intro n hn
    simp only [refsOf] at ⊢
    cases hre : resolveSlicesT wt fuel e with
    | concat parts => exact (hnc parts hre).elim
    | ref n' => exact (hnr n' hre).elim
    | slice i a b => exact (hns i a b hre).elim
    | const cv cw =>
      rw [hre] at hn
      simp [refsOf] at hn
    | op o args =>
      rw [hre] at hn
      simp only [refsOf] at hn
      have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
        rw [hre]; simpa [refsOf] using hn
      exact ih1 n h2
    | sliceDim i d j =>
      rw [hre] at hn
      simp only [refsOf] at hn
      have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
        rw [hre]; simpa [refsOf] using hn
      exact ih1 n h2
    | index a i =>
      rw [hre] at hn
      simp only [refsOf] at hn
      have h2 : n ∈ refsOf (resolveSlicesT wt fuel e) := by
        rw [hre]; simpa [refsOf] using hn
      exact ih1 n h2
  | case13 x e h0 h1 h2 h3 h4 =>
    match x, h0 with
    | fuel + 1, _ =>
      cases e with
      | op o args => exact (h2 fuel o args rfl rfl).elim
      | concat args => exact (h3 fuel args rfl rfl).elim
      | slice s a b => exact (h4 fuel s a b rfl rfl).elim
      | const cv cw => rw [rsT_const]; exact fun n hn => hn
      | ref n => rw [rsT_ref]; exact fun n hn => hn
      | sliceDim i d j => rw [rsT_sliceDim]; exact fun n hn => hn
      | index a i => rw [rsT_index]; exact fun n hn => hn
  | case14 fuel n hn =>
    rw [rsTL_nil] at hn
    exact hn
  | case15 fuel a rest ih2 ih1 n hn =>
    rw [rsTL_cons] at hn
    simp only [refsOf.refsList, List.mem_append] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (ih2 n hn)
    · exact Or.inr (ih1 n hn)

/-- A fully-inlined cone only references stop-set names. -/
theorem inlineConeT_refs (dm : DefMap) (stopAt : Std.HashMap String Bool) :
    ∀ fuel e, (∀ e', inlineConeT dm stopAt fuel e = .ok e' →
      ∀ n ∈ refsOf e', stopAt.contains n = true) := by
  intro fuel e
  induction fuel, e using inlineConeT.induct dm stopAt
    (motive2 := fun fuel args => ∀ args',
      inlineConeTL dm stopAt fuel args = .ok args' →
      ∀ n ∈ refsOf.refsList args', stopAt.contains n = true) with
  | case1 fuel n hs =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_pos] at h
    cases h
    intro m hm
    simp only [refsOf, List.mem_singleton] at hm
    subst hm
    exact hs
  | case2 n hs =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, Bool.false_eq_true, ite_false] at h
    simp at h
  | case3 fuel n hs hdm hf =>
    intro e' h
    match fuel, hf with
    | fuel + 1, _ =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp only [hs, Bool.false_eq_true, ite_false, hdm] at h
      simp at h
  | case4 n hs fuel rhs hdm ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, Bool.false_eq_true, ite_false, hdm] at h
    exact ih e' h
  | case5 fuel o args ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind] at h
      subst h
      intro n hn
      exact ih args' hl n (by simpa [refsOf] using hn)
  | case6 fuel args ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind] at h
      subst h
      intro n hn
      exact ih args' hl n (by simpa [refsOf] using hn)
  | case7 fuel e hi lo ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases he : inlineConeT dm stopAt fuel e with
    | error err => rw [he] at h; simp [Bind.bind, Except.bind] at h
    | ok e0 =>
      rw [he] at h
      simp [Bind.bind, Except.bind] at h
      subst h
      intro n hn
      exact ih e0 he n (by simpa [refsOf] using hn)
  | case8 x array idx =>
    intro e' h
    rw [inlineConeT.eq_def] at h; simp at h
  | case9 x expr hi lo =>
    intro e' h
    rw [inlineConeT.eq_def] at h; simp at h
  | case10 x e hne1 hne2 hne3 hne4 hne5 hne6 =>
    intro e' h
    cases e with
    | ref n => exact absurd rfl (hne1 n)
    | op o args => exact absurd rfl (hne2 o args)
    | concat args => exact absurd rfl (hne3 args)
    | slice e hi lo => exact absurd rfl (hne4 e hi lo)
    | index a i => exact absurd rfl (hne5 a i)
    | sliceDim e hi lo => exact absurd rfl (hne6 e hi lo)
    | const v w =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp at h
      subst h
      intro n hn
      simp [refsOf] at hn
  | case11 x args' h n hn =>
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    simp at h
    subst h
    simp [refsOf.refsList] at hn
  | case12 fuel a rest iha ihrest args' h n hn =>
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    cases ha : inlineConeT dm stopAt fuel a with
    | error err => rw [ha] at h; simp [Bind.bind, Except.bind] at h
    | ok a' =>
      rw [ha] at h
      cases hr : inlineConeTL dm stopAt fuel rest with
      | error err => rw [hr] at h; simp [Bind.bind, Except.bind] at h
      | ok rest' =>
        rw [hr] at h
        simp [Bind.bind, Except.bind] at h
        subst h
        simp only [refsOf.refsList, List.mem_append] at hn
        rcases hn with hn | hn
        · exact iha a' ha n hn
        · exact ihrest rest' hr n hn

/- ---- decidable checkers for the capstone's hypotheses ---- -/

/-- Boolean mirror of `memFree`. -/
def memFreeCheck : List Stmt → Bool
  | [] => true
  | .memory .. :: _ => false
  | _ :: rest => memFreeCheck rest

theorem memFreeCheck_sound :
    ∀ body, memFreeCheck body = true → memFree body
  | [], _ => trivial
  | .assign .. :: rest, h => memFreeCheck_sound rest (by simpa [memFreeCheck] using h)
  | .register .. :: rest, h => memFreeCheck_sound rest (by simpa [memFreeCheck] using h)
  | .memory .. :: _, h => by simp [memFreeCheck] at h
  | .inst .. :: rest, h => memFreeCheck_sound rest (by simpa [memFreeCheck] using h)

/-- Boolean mirror of `noSelfRead`. -/
def noSelfReadCheck : List Stmt → Bool
  | [] => true
  | s :: rest =>
    (stmtReads s).all (fun n => !(stmtWrites s).contains n)
      && noSelfReadCheck rest

theorem noSelfReadCheck_sound :
    ∀ body, noSelfReadCheck body = true → noSelfRead body
  | [], _ => trivial
  | s :: rest, h => by
    simp only [noSelfReadCheck, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fun n hn hw => by
        have := h.1 n hn
        simp at this
        exact this hw,
      noSelfReadCheck_sound rest h.2⟩

/-- Boolean mirror of the capstone's `hwf` (assignment-width
    discipline), stated over the body list. -/
def hwfCheck (we : WEnv) (stopAt : Std.HashMap String Bool) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (stopAt.contains l || widthOf we r == we l) && hwfCheck we stopAt rest
  | _ :: rest => hwfCheck we stopAt rest

theorem hwfCheck_mem (we : WEnv) (stopAt : Std.HashMap String Bool) :
    ∀ body, hwfCheck we stopAt body = true →
    ∀ n rhs, Stmt.assign n rhs ∈ body →
      stopAt.contains n = false → widthOf we rhs = we n
  | [], _, n, rhs, hin, _ => by simp at hin
  | s :: rest, h, n, rhs, hin, hns => by
    cases hin with
    | head =>
      simp only [hwfCheck, Bool.and_eq_true, Bool.or_eq_true,
        beq_iff_eq] at h
      rcases h.1 with hc | hc
      · rw [hns] at hc; simp at hc
      · exact hc
    | tail _ hin' =>
      cases s with
      | assign l r =>
        simp only [hwfCheck, Bool.and_eq_true] at h
        exact hwfCheck_mem we stopAt rest h.2 n rhs hin' hns
      | register o c rs i iv =>
        exact hwfCheck_mem we stopAt rest (by simpa [hwfCheck] using h)
          n rhs hin' hns
      | memory a b c d e f g i j k m nn =>
        exact hwfCheck_mem we stopAt rest (by simpa [hwfCheck] using h)
          n rhs hin' hns
      | inst a b c =>
        exact hwfCheck_mem we stopAt rest (by simpa [hwfCheck] using h)
          n rhs hin' hns

theorem hwfCheck_sound (we : WEnv) (stopAt : Std.HashMap String Bool)
    (body : List Stmt) (h : hwfCheck we stopAt body = true) :
    ∀ n rhs, (buildDefMap body).get? n = some rhs →
      stopAt.contains n = false → widthOf we rhs = we n := by
  intro n rhs hget hns
  rcases buildDefMap_mem body {} n rhs hget with hin | hempty
  · exact hwfCheck_mem we stopAt body h n rhs hin hns
  · simp at hempty

/-- Boolean mirror of "the combinational fold never writes a stop-set
    name" (inputs and registers are not assign targets). -/
def stopAtFrozenCheck (stopAt : Std.HashMap String Bool) :
    List Stmt → Bool
  | [] => true
  | s :: rest =>
    (stmtWrites s).all (fun n => !stopAt.contains n)
      && stopAtFrozenCheck stopAt rest

theorem stopAtFrozenCheck_sound (stopAt : Std.HashMap String Bool) :
    ∀ body, stopAtFrozenCheck stopAt body = true →
    ∀ n, stopAt.contains n = true → n ∉ writesOf body
  | [], _, n, _ => by simp [writesOf]
  | s :: rest, h, n, hc => by
    simp only [stopAtFrozenCheck, Bool.and_eq_true, List.all_eq_true] at h
    intro hin
    simp only [writesOf, List.flatMap_cons, List.mem_append] at hin
    rcases hin with hin | hin
    · have := h.1 n hin
      rw [hc] at this
      simp at this
    · exact stopAtFrozenCheck_sound stopAt rest h.2 n hc
        (by simpa [writesOf] using hin)

/- ---- the seed-side capstone ---- -/

/-- THE BRIDGE FORM of the capstone: the resolved inlined cone
    evaluated in the SEED environment (what the generated `irTrace`
    recurrence actually does) still equals the fold's value — the cone
    only reads stop-set names, and the fold never writes those.

    Boundedness is required of the SEED only (`hb0`): the inlined cone
    is moved back to `env0` by the frame/congruence argument BEFORE
    slice resolution is applied, so nothing about the fold's own
    writes is needed.  Per instance `hb0` is immediate — registers by
    the generated `irTrace_bound`, inputs by `BitVec.isLt`, all other
    names 0. -/
theorem cone_resolved_agrees_at_seed (we : WEnv) (mems : MEnv)
    {done : List String} {body : List Stmt} {env0 env1 : Env}
    (stopAt : Std.HashMap String Bool) (wt : Std.HashMap String Nat)
    (hWO : WO done body)
    (hm : memFree body) (hsr : noSelfRead body)
    (hrun : evalAssigns we mems body env0 = some env1)
    (hwf : ∀ n rhs, (buildDefMap body).get? n = some rhs →
      stopAt.contains n = false → widthOf we rhs = we n)
    (hwt : ∀ n w, wt.get? n = some w → we n = w)
    (hb0 : ∀ n, env0 n < 2 ^ we n)
    (hfrozen : ∀ n, stopAt.contains n = true → n ∉ writesOf body)
    {fuel : Nat} {e e' : Expr}
    (hinl : inlineConeT (buildDefMap body) stopAt fuel e = .ok e')
    (rfuel : Nat) {v : Nat} (hv : evalExpr we env1 e = some v) :
    evalExpr we env0 (resolveSlicesT wt rfuel e') = some v := by
  have h1 : evalExpr we env1 e' = some v := by
    rw [cone_agrees_with_fold we mems stopAt hWO hm hsr hrun hwf hinl]
    exact hv
  have h0 : evalExpr we env0 e' = some v := by
    rw [evalExpr_congr we env0 env1 e' (fun n hn =>
      (evalAssigns_frame we mems body env0 env1 hrun hm n
        (hfrozen n (inlineConeT_refs (buildDefMap body) stopAt fuel e e'
          hinl n hn))).symm)]
    exact h1
  exact resolveSlicesT_eval wt we env0 hwt hb0 rfuel e' v h0

/- ---- per-instance width-table plumbing ---- -/

/-- A binding in an assoc-list-built map came from the list. -/
theorem assocMap_mem :
    ∀ (l : List (String × Nat)) (m0 : Std.HashMap String Nat)
      (n : String) (w : Nat),
    (l.foldl (fun m p => m.insert p.1 p.2) m0).get? n = some w →
    (n, w) ∈ l ∨ m0.get? n = some w
  | [], _, _, _, h => Or.inr h
  | p :: rest, m0, n, w, h => by
    simp only [List.foldl_cons] at h
    rcases assocMap_mem rest (m0.insert p.1 p.2) n w h with hin | hm0
    · exact Or.inl (List.mem_cons_of_mem _ hin)
    · simp only [Std.HashMap.get?_insert] at hm0
      split at hm0
      · rename_i heq
        simp only [Option.some_inj] at hm0
        left
        obtain ⟨a, b⟩ := p
        simp only [beq_iff_eq] at heq
        subst heq
        subst hm0
        exact List.mem_cons_self ..
      · exact Or.inr hm0

/-- The capstone's `hwt` from a finite width list: if the width env
    agrees with every listed pair, it agrees with the map built from
    the list.  The premise is a decidable finite conjunction. -/
theorem hwt_of_assoc (we : WEnv) (l : List (String × Nat))
    (h : ∀ p ∈ l, we p.1 = p.2) :
    ∀ n w, (l.foldl (fun m p => m.insert p.1 p.2)
        ({} : Std.HashMap String Nat)).get? n = some w → we n = w := by
  intro n w hget
  rcases assocMap_mem l {} n w hget with hin | hempty
  · exact h (n, w) hin
  · simp at hempty

/- ---- width-environment congruence ----
   `evalExpr` consults the width environment ONLY at `.ref` nodes
   (through `widthOf`, including the widths `evalOp`'s not/asr/signed
   arms and the concat combiner read).  Two width envs agreeing on an
   expression's references evaluate it identically — the deep pipeline
   needs this to move between its register+input-keyed `weOfC` and the
   full-width-table env the bridge theorems require. -/

theorem refsList_mem :
    ∀ (args : List Expr) (a : Expr), a ∈ args →
    ∀ n ∈ refsOf a, n ∈ refsOf.refsList args
  | [], _, ha, _, _ => by simp at ha
  | b :: rest, a, ha, n, hn => by
    simp only [refsOf.refsList, List.mem_append]
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact Or.inl hn
    · exact Or.inr (refsList_mem rest a h n hn)

mutual
theorem widthOf_we_congr (we we' : WEnv) :
    ∀ (e : Expr), (∀ n ∈ refsOf e, we n = we' n) →
      widthOf we e = widthOf we' e
  | .const .., _ => rfl
  | .ref n, h => by simp [widthOf, h n (by simp [refsOf])]
  | .op o args, h => by
    have hl : ∀ a ∈ args, widthOf we a = widthOf we' a := fun a ha =>
      widthOf_we_congr we we' a (fun n hn => h n (by
        simp only [refsOf]
        exact refsList_mem args a ha n hn))
    cases o <;>
      (cases args with
       | nil => rfl
       | cons a1 t1 =>
         cases t1 with
         | nil => simp [widthOf, hl a1 (by simp)]
         | cons a2 t2 =>
           cases t2 with
           | nil => simp [widthOf, hl a1 (by simp), hl a2 (by simp)]
           | cons a3 t3 =>
             cases t3 with
             | nil => simp [widthOf, hl a1 (by simp), hl a2 (by simp),
                 hl a3 (by simp)]
             | cons a4 t4 => simp [widthOf])
  | .concat args, h => by
    simp only [widthOf]
    exact widthOfGo_we_congr we we' args (fun a ha n hn =>
      h n (by simp only [refsOf]; exact refsList_mem args a ha n hn))
  | .slice e hi lo, _ => rfl
  | .sliceDim .., _ => rfl
  | .index .., _ => rfl

theorem widthOfGo_we_congr (we we' : WEnv) :
    ∀ (args : List Expr),
      (∀ a ∈ args, ∀ n ∈ refsOf a, we n = we' n) →
      widthOf.go we args = widthOf.go we' args
  | [], _ => rfl
  | a :: rest, h => by
    simp only [widthOf.go,
      widthOf_we_congr we we' a (h a (by simp)),
      widthOfGo_we_congr we we' rest (fun b hb => h b (by simp [hb]))]
end

theorem zipFoldW_we_congr (we we' : WEnv) :
    ∀ (as : List Expr), (∀ a ∈ as, widthOf we a = widthOf we' a) →
    ∀ (vs : List Nat) (acc : Nat),
      ((as.zip vs).foldl (fun a (p : Expr × Nat) =>
        a + widthOf we p.1) acc)
      = ((as.zip vs).foldl (fun a (p : Expr × Nat) =>
        a + widthOf we' p.1) acc)
  | [], _, _, _ => rfl
  | a :: as', h, vs, acc => by
    cases vs with
    | nil => rfl
    | cons v vs' =>
      simp only [List.zip_cons_cons, List.foldl_cons, h a (by simp)]
      exact zipFoldW_we_congr we we' as' (fun b hb => h b (by simp [hb]))
        vs' _

theorem evalOp_we_congr (we we' : WEnv) (o : Operator) :
    ∀ (args : List Expr),
      (∀ a ∈ args, widthOf we a = widthOf we' a) →
      ∀ (vals : List Nat) (w : Nat),
      evalOp we o args vals w = evalOp we' o args vals w := by
  intro args h vals w
  cases o <;>
    (cases args with
     | nil =>
       (cases vals with
         | nil => simp_all [evalOp]
         | cons v1 u1 =>
           cases u1 with
           | nil => simp_all [evalOp]
           | cons v2 u2 =>
             cases u2 with
             | nil => simp_all [evalOp]
             | cons v3 u3 =>
               cases u3 with
               | nil => simp_all [evalOp]
               | cons v4 u4 => simp_all [evalOp])
     | cons a1 t1 =>
       have h1 := h a1 (by simp)
       cases t1 with
       | nil =>
         (cases vals with
           | nil => simp_all [evalOp]
           | cons v1 u1 =>
             cases u1 with
             | nil => simp_all [evalOp]
             | cons v2 u2 =>
               cases u2 with
               | nil => simp_all [evalOp]
               | cons v3 u3 =>
                 cases u3 with
                 | nil => simp_all [evalOp]
                 | cons v4 u4 => simp_all [evalOp])
       | cons a2 t2 =>
         have h2 := h a2 (by simp)
         cases t2 with
         | nil =>
           (cases vals with
             | nil => simp_all [evalOp]
             | cons v1 u1 =>
               cases u1 with
               | nil => simp_all [evalOp]
               | cons v2 u2 =>
                 cases u2 with
                 | nil => simp_all [evalOp]
                 | cons v3 u3 =>
                   cases u3 with
                   | nil => simp_all [evalOp]
                   | cons v4 u4 => simp_all [evalOp])
         | cons a3 t3 =>
           cases t3 with
           | nil =>
             (cases vals with
               | nil => simp_all [evalOp]
               | cons v1 u1 =>
                 cases u1 with
                 | nil => simp_all [evalOp]
                 | cons v2 u2 =>
                   cases u2 with
                   | nil => simp_all [evalOp]
                   | cons v3 u3 =>
                     cases u3 with
                     | nil => simp_all [evalOp]
                     | cons v4 u4 => simp_all [evalOp])
           | cons a4 t4 =>
             (cases vals with
               | nil => simp_all [evalOp]
               | cons v1 u1 =>
                 cases u1 with
                 | nil => simp_all [evalOp]
                 | cons v2 u2 =>
                   cases u2 with
                   | nil => simp_all [evalOp]
                   | cons v3 u3 =>
                     cases u3 with
                     | nil => simp_all [evalOp]
                     | cons v4 u4 => simp_all [evalOp]))

theorem evalGo_we_congr (we we' : WEnv) :
    ∀ (args : List Expr), (∀ a ∈ args, widthOf we a = widthOf we' a) →
    ∀ (vals : List Nat),
      evalExpr.go we args vals = evalExpr.go we' args vals
  | [], _, _ => rfl
  | a :: rest, h, vals => by
    cases vals with
    | nil => rfl
    | cons v vs =>
      simp only [evalExpr.go, h a (by simp),
        zipFoldW_we_congr we we' rest
          (fun b hb => h b (by simp [hb])) vs,
        evalGo_we_congr we we' rest (fun b hb => h b (by simp [hb])) vs]

mutual
/-- Two width environments agreeing on an expression's references
    evaluate it identically. -/
theorem evalExpr_we_congr (we we' : WEnv) (env : Env) :
    ∀ (e : Expr), (∀ n ∈ refsOf e, we n = we' n) →
      evalExpr we env e = evalExpr we' env e
  | .const .., _ => rfl
  | .ref .., _ => rfl
  | .op o args, h => by
    have hargs := evalList_we_congr we we' env args
      (fun a ha n hn => h n (by
        simp only [refsOf]; exact refsList_mem args a ha n hn))
    have hwl : ∀ a ∈ args, widthOf we a = widthOf we' a := fun a ha =>
      widthOf_we_congr we we' a (fun n hn => h n (by
        simp only [refsOf]; exact refsList_mem args a ha n hn))
    have hw := widthOf_we_congr we we' (.op o args) h
    simp only [evalExpr, hargs, hw]
    cases evalList we' env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [evalOp_we_congr we we' o args hwl vals _]
  | .concat args, h => by
    have hargs := evalList_we_congr we we' env args
      (fun a ha n hn => h n (by
        simp only [refsOf]; exact refsList_mem args a ha n hn))
    have hwl : ∀ a ∈ args, widthOf we a = widthOf we' a := fun a ha =>
      widthOf_we_congr we we' a (fun n hn => h n (by
        simp only [refsOf]; exact refsList_mem args a ha n hn))
    simp only [evalExpr, hargs]
    cases evalList we' env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        evalGo_we_congr we we' args hwl vals]
  | .slice e hi lo, h => by
    simp only [evalExpr,
      evalExpr_we_congr we we' env e (by simpa [refsOf] using h)]
  | .sliceDim .., _ => rfl
  | .index .., _ => rfl

theorem evalList_we_congr (we we' : WEnv) (env : Env) :
    ∀ (args : List Expr),
      (∀ a ∈ args, ∀ n ∈ refsOf a, we n = we' n) →
      evalList we env args = evalList we' env args
  | [], _ => rfl
  | a :: rest, h => by
    simp only [evalList,
      evalExpr_we_congr we we' env a (h a (by simp)),
      evalList_we_congr we we' env rest (fun b hb => h b (by simp [hb]))]
end

/- ---- concatNorm preservation ----
   The deep pipeline quotes its cones through
   `Tools.ConcatNorm.concatNorm` (binary-cat normalization matching
   `CExpr.compile`'s output shape).  `norm2` collapses a SINGLETON
   concat to its bare element — unmasked — so semantics are preserved
   only on singleton-free expressions; real cones never contain one
   (decidable `noSingle`, discharged per instance). -/

section ConcatNormBridge

open Tools.ConcatNorm

mutual
def noSingle : Expr → Bool
  | .concat args => args.length != 1 && noSingleL args
  | .op _ args => noSingleL args
  | .slice e _ _ => noSingle e
  | .sliceDim e _ _ => noSingle e
  | .index a i => noSingle a && noSingle i
  | _ => true

def noSingleL : List Expr → Bool
  | [] => true
  | a :: rest => noSingle a && noSingleL rest
end

theorem noSingleL_mem :
    ∀ (args : List Expr), noSingleL args = true →
    ∀ a ∈ args, noSingle a = true
  | [], _, a, ha => by simp at ha
  | b :: rest, h, a, ha => by
    simp only [noSingleL, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with heq | hm
    · subst heq; exact h.1
    · exact noSingleL_mem rest h.2 a hm

theorem cN_zero (e : Expr) : concatNorm 0 e = e := by
  rw [concatNorm.eq_def]

theorem cN_op (fuel : Nat) (o : Operator) (args : List Expr) :
    concatNorm (fuel + 1) (.op o args)
      = .op o (concatNormL fuel args) := by
  rw [concatNorm.eq_def]

theorem cN_concat (fuel : Nat) (args : List Expr) :
    concatNorm (fuel + 1) (.concat args)
      = norm2 (concatNormL fuel args) := by
  rw [concatNorm.eq_def]

theorem cN_slice (fuel : Nat) (e : Expr) (hi lo : Nat) :
    concatNorm (fuel + 1) (.slice e hi lo)
      = .slice (concatNorm fuel e) hi lo := by
  rw [concatNorm.eq_def]

theorem cN_const (fuel : Nat) (v : Int) (w : Nat) :
    concatNorm (fuel + 1) (.const v w) = .const v w := by
  rw [concatNorm.eq_def]

theorem cN_ref (fuel : Nat) (n : String) :
    concatNorm (fuel + 1) (.ref n) = .ref n := by
  rw [concatNorm.eq_def]

theorem cN_sliceDim (fuel : Nat) (e : Expr)
    (d i : Sparkle.IR.Type.DimExpr) :
    concatNorm (fuel + 1) (.sliceDim e d i) = .sliceDim e d i := by
  rw [concatNorm.eq_def]

theorem cN_index (fuel : Nat) (a i : Expr) :
    concatNorm (fuel + 1) (.index a i) = .index a i := by
  rw [concatNorm.eq_def]

theorem cNL_nil (fuel : Nat) : concatNormL fuel [] = [] := by
  rw [concatNormL.eq_def]

theorem cNL_cons (fuel : Nat) (a : Expr) (rest : List Expr) :
    concatNormL fuel (a :: rest)
      = concatNorm fuel a :: concatNormL fuel rest := by
  rw [concatNormL.eq_def]

theorem cNL_length (fuel : Nat) :
    ∀ (args : List Expr), (concatNormL fuel args).length = args.length
  | [] => by rw [cNL_nil]
  | a :: rest => by
    rw [cNL_cons]
    simp [cNL_length fuel rest]

theorem norm2_width_all (we : WEnv) :
    ∀ (l : List Expr), l.length ≠ 1 →
      widthOf we (norm2 l) = widthOf we (.concat l)
  | [], _ => rfl
  | [a], h => by simp at h
  | a :: b :: rest, _ => norm2_width we a b rest

theorem norm2_eval_all (we : WEnv) (env : Env) :
    ∀ (l : List Expr), l.length ≠ 1 →
      evalExpr we env (norm2 l) = evalExpr we env (.concat l)
  | [], _ => rfl
  | [a], h => by simp at h
  | a :: b :: rest, _ => norm2_eval we env a b rest

theorem norm2_refs :
    ∀ (l : List Expr), refsOf (norm2 l) = refsOf.refsList l
  | [] => rfl
  | [a] => by simp [norm2, refsOf.refsList]
  | a :: b :: rest => by
    show refsOf (.concat [a, norm2 (b :: rest)]) = _
    simp only [refsOf, refsOf.refsList, norm2_refs (b :: rest),
      List.append_nil]

/-- `concatNorm` preserves widths on singleton-free expressions. -/
theorem concatNorm_width (we : WEnv) :
    ∀ fuel e, noSingle e = true →
      widthOf we (concatNorm fuel e) = widthOf we e := by
  intro fuel e
  induction fuel, e using concatNorm.induct
    (motive_2 := fun fuel args => noSingleL args = true →
      WidthMatch we args (concatNormL fuel args)) with
  | case1 e =>
    intro _
    rw [cN_zero]
  | case2 fuel o args ih =>
    intro hns
    rw [cN_op]
    simp only [noSingle] at hns
    exact widthOf_op_shape we o (ih hns)
  | case3 fuel args ih =>
    intro hns
    rw [cN_concat]
    simp only [noSingle, Bool.and_eq_true, bne_iff_ne] at hns
    rw [norm2_width_all we _ (by rw [cNL_length]; exact hns.1)]
    simp only [widthOf]
    exact widthOfGo_congr we (ih hns.2)
  | case4 fuel e hi lo ih =>
    intro _
    rw [cN_slice]
    simp [widthOf]
  | case5 x e h1 h2 h3 =>
    intro _
    cases e with
    | op o args => exact (h1 o args rfl).elim
    | concat args => exact (h2 args rfl).elim
    | slice s a b => exact (h3 s a b rfl).elim
    | const v w => rw [cN_const]
    | ref n => rw [cN_ref]
    | sliceDim i d j => rw [cN_sliceDim]
    | index a i => rw [cN_index]
  | case6 fuel hns =>
    rw [cNL_nil]
    exact .nil
  | case7 fuel a rest iha ihrest hns =>
    simp only [noSingleL, Bool.and_eq_true] at hns
    rw [cNL_cons]
    exact .cons (iha hns.1) (ihrest hns.2)

theorem concatNormL_widthMatch (we : WEnv) (fuel : Nat) :
    ∀ (args : List Expr), noSingleL args = true →
      WidthMatch we args (concatNormL fuel args)
  | [], _ => by rw [cNL_nil]; exact .nil
  | a :: rest, h => by
    simp only [noSingleL, Bool.and_eq_true] at h
    rw [cNL_cons]
    exact .cons (concatNorm_width we fuel a h.1)
      (concatNormL_widthMatch we fuel rest h.2)

/-- `concatNorm` preserves evaluation on singleton-free expressions. -/
theorem concatNorm_eval (we : WEnv) (env : Env) :
    ∀ fuel e, noSingle e = true →
      evalExpr we env (concatNorm fuel e) = evalExpr we env e := by
  intro fuel e
  induction fuel, e using concatNorm.induct
    (motive_2 := fun fuel args => noSingleL args = true →
      evalList we env (concatNormL fuel args) = evalList we env args) with
  | case1 e =>
    intro _
    rw [cN_zero]
  | case2 fuel o args ih =>
    intro hns
    rw [cN_op]
    simp only [noSingle] at hns
    have hwm := concatNormL_widthMatch we fuel args hns
    simp only [evalExpr, ih hns, widthOf_op_shape we o hwm]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [evalOp_congr we hwm o vals _]
  | case3 fuel args ih =>
    intro hns
    rw [cN_concat]
    simp only [noSingle, Bool.and_eq_true, bne_iff_ne] at hns
    have hwm := concatNormL_widthMatch we fuel args hns.2
    rw [norm2_eval_all we env _ (by rw [cNL_length]; exact hns.1)]
    simp only [evalExpr, ih hns.2]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        evalGo_congr we hwm vals]
  | case4 fuel e hi lo ih =>
    intro hns
    rw [cN_slice]
    simp only [noSingle] at hns
    simp only [evalExpr, ih hns]
  | case5 x e h1 h2 h3 =>
    intro _
    cases e with
    | op o args => exact (h1 o args rfl).elim
    | concat args => exact (h2 args rfl).elim
    | slice s a b => exact (h3 s a b rfl).elim
    | const v w => rw [cN_const]
    | ref n => rw [cN_ref]
    | sliceDim i d j => rw [cN_sliceDim]
    | index a i => rw [cN_index]
  | case6 fuel hns =>
    rw [cNL_nil]
  | case7 fuel a rest iha ihrest hns =>
    simp only [noSingleL, Bool.and_eq_true] at hns
    rw [cNL_cons]
    simp only [evalList, iha hns.1, ihrest hns.2]

/-- Normalization never introduces a reference. -/
theorem concatNorm_refs :
    ∀ fuel e, ∀ n ∈ refsOf (concatNorm fuel e), n ∈ refsOf e := by
  intro fuel e
  induction fuel, e using concatNorm.induct
    (motive_2 := fun fuel args =>
      ∀ n ∈ refsOf.refsList (concatNormL fuel args),
        n ∈ refsOf.refsList args) with
  | case1 e =>
    rw [cN_zero]
    exact fun n hn => hn
  | case2 fuel o args ih =>
    rw [cN_op]
    intro n hn
    simp only [refsOf] at hn ⊢
    exact ih n hn
  | case3 fuel args ih =>
    rw [cN_concat]
    intro n hn
    rw [norm2_refs] at hn
    simp only [refsOf]
    exact ih n hn
  | case4 fuel e hi lo ih =>
    rw [cN_slice]
    intro n hn
    simp only [refsOf] at hn ⊢
    exact ih n hn
  | case5 x e h1 h2 h3 =>
    cases e with
    | op o args => exact (h1 o args rfl).elim
    | concat args => exact (h2 args rfl).elim
    | slice s a b => exact (h3 s a b rfl).elim
    | const v w => rw [cN_const]; exact fun n hn => hn
    | ref nn => rw [cN_ref]; exact fun n hn => hn
    | sliceDim i d j => rw [cN_sliceDim]; exact fun n hn => hn
    | index a i => rw [cN_index]; exact fun n hn => hn
  | case6 fuel n hn =>
    rw [cNL_nil] at hn
    exact hn
  | case7 fuel a rest iha ihrest n hn =>
    rw [cNL_cons] at hn
    simp only [refsOf.refsList, List.mem_append] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (iha n hn)
    · exact Or.inr (ihrest n hn)

end ConcatNormBridge

/- ---- the cycle-level iteration ---- -/

/-- Upward-counting register-state iteration of the module step
    (wall-clock indices, unlike `runModule`'s countdown): `seed t st`
    builds cycle `t`'s starting environment from the register state.
    The generated `{base}_state_trace` theorems relate this to the
    `irTrace` recurrence by induction. -/
def stepIter (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) :
    Nat → Option (String → Nat)
  | 0 => some st0
  | t + 1 => do
    let st ← stepIter we body seed st0 t
    let (_, nexts, _) ← stepModule we body (seed t st) (fun _ _ => 0)
    some (applyNexts st nexts)

/-- On a memory-free body the memory phase is the identity. -/
theorem memNexts_memFree (we : WEnv) :
    ∀ (body : List Stmt), memFree body →
    ∀ (mems : MEnv) (env : Env), memNexts we body mems env = some mems
  | [], _, _, _ => rfl
  | .assign .. :: rest, hm, mems, env =>
    memNexts_memFree we rest (by simpa [memFree] using hm) mems env
  | .register .. :: rest, hm, mems, env =>
    memNexts_memFree we rest (by simpa [memFree] using hm) mems env
  | .memory .. :: _, hm, _, _ => by simp [memFree] at hm
  | .inst .. :: rest, hm, mems, env =>
    memNexts_memFree we rest (by simpa [memFree] using hm) mems env

/- ---- stepIter ↔ runModule reindexing ----
   `runModule` (the object the certified Arc-2 capstones are stated
   over) seeds with a COUNTDOWN index; the generated `state_trace` /
   `signal_fold` theorems run over the wall-clock-indexed `stepIter`.
   These lemmas connect the two once and for all. -/

theorem stepIter_seed_congr (we : WEnv) (body : List Stmt)
    (s1 s2 : Nat → (String → Nat) → Env) (st0 : String → Nat) :
    ∀ (j : Nat), (∀ t, t < j → s1 t = s2 t) →
    stepIter we body s1 st0 j = stepIter we body s2 st0 j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [stepIter, Option.bind_eq_bind]
    rw [stepIter_seed_congr we body s1 s2 st0 j
      (fun t ht => h t (by omega))]
    cases hs : stepIter we body s2 st0 j with
    | none => rfl
    | some st =>
      simp only [Option.bind_some]
      rw [h j (by omega)]

theorem runModule_seed_congr (we : WEnv) (body : List Stmt) :
    ∀ (k : Nat) (s1 s2 : Nat → (String → Nat) → Env),
    (∀ td, td < k → s1 td = s2 td) →
    ∀ (st : String → Nat) (mems : MEnv),
    runModule we body s1 k st mems = runModule we body s2 k st mems
  | 0, _, _, _, _, _ => rfl
  | k + 1, s1, s2, h, st, mems => by
    simp only [runModule, Option.bind_eq_bind]
    rw [h k (by omega)]
    cases hs : stepModule we body (s2 k st) mems with
    | none => rfl
    | some trip =>
      simp only [Option.bind_some]
      rw [runModule_seed_congr we body k s1 s2
        (fun td htd => h td (by omega))]

/-- One-step (rear) unfold of the iteration, as an equation. -/
theorem stepIter_succ (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (j : Nat) :
    stepIter we body seed st0 (j + 1) = (do
      let st ← stepIter we body seed st0 j
      let (_, nexts, _) ← stepModule we body (seed j st) (fun _ _ => 0)
      some (applyNexts st nexts)) := rfl

/-- Peel the FIRST step off the upward iteration (`stepIter` recurses
    on the last). -/
theorem stepIter_succ_front (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (st0 : String → Nat)
    {envF : Env} {nexts : List (String × Nat)} {mems' : MEnv}
    (hstep : stepModule we body (seed 0 st0) (fun _ _ => 0)
      = some (envF, nexts, mems')) :
    ∀ (j : Nat),
    stepIter we body seed st0 (j + 1)
      = stepIter we body (fun t s => seed (t + 1) s)
          (applyNexts st0 nexts) j
  | 0 => by
    simp only [stepIter, Option.bind_eq_bind, Option.bind_some, hstep]
  | j + 1 => by
    rw [stepIter_succ we body seed st0 (j + 1),
        stepIter_succ_front we body seed st0 hstep j,
        stepIter_succ we body (fun t s => seed (t + 1) s)
          (applyNexts st0 nexts) j]

/-- THE REINDEXING: a successful `runModule` run under the reversed
    (wall-clock) seed produces, at position `j`, exactly the
    combinational environment of `stepIter`'s cycle `j`. -/
theorem runModule_stepIter (we : WEnv) (body : List Stmt)
    (hm : memFree body) (seedUp : Nat → (String → Nat) → Env) :
    ∀ (k off : Nat) (st : String → Nat) (envs : List Env),
    runModule we body (fun td s => seedUp (off + (k - 1 - td)) s) k st
      (fun _ _ => 0) = some envs →
    ∀ j, j < k →
    ∃ (st' : String → Nat) (env1 : Env),
      stepIter we body (fun t s => seedUp (off + t) s) st j = some st'
        ∧ evalAssigns we (fun _ _ => 0) body (seedUp (off + j) st')
            = some env1
        ∧ envs[j]? = some env1
  | 0, _, _, _, _, j, hj => by omega
  | k + 1, off, st, envs, hrunM, j, hj => by
    simp only [runModule, Option.bind_eq_bind] at hrunM
    cases hs : stepModule we body
        (seedUp (off + (k + 1 - 1 - k)) st) (fun _ _ => 0) with
    | none => rw [hs] at hrunM; simp at hrunM
    | some trip =>
      obtain ⟨envF, nexts, mems'⟩ := trip
      rw [hs] at hrunM
      simp only [Option.bind_some] at hrunM
      cases hrest : runModule we body
          (fun td s => seedUp (off + (k + 1 - 1 - td)) s) k
          (applyNexts st nexts) mems' with
      | none => rw [hrest] at hrunM; simp at hrunM
      | some restEnvs =>
        rw [hrest] at hrunM
        simp only [Option.bind_some, Option.some_inj] at hrunM
        subst hrunM
        -- the head step is wall-clock `off`
        have hoff : off + (k + 1 - 1 - k) = off := by omega
        rw [hoff] at hs
        -- decompose the head step once
        simp only [stepModule, Option.bind_eq_bind] at hs
        cases hA : evalAssigns we (fun _ _ => 0) body
            (seedUp off st) with
        | none => rw [hA] at hs; simp at hs
        | some envA =>
          rw [hA] at hs
          simp only [Option.bind_some] at hs
          cases hN : regNexts we (fun _ _ => 0) body envA with
          | none => rw [hN] at hs; simp at hs
          | some nx =>
            rw [hN] at hs
            rw [memNexts_memFree we body hm] at hs
            simp only [Option.bind_some, Option.some_inj,
              Prod.mk.injEq] at hs
            obtain ⟨hEnvF, hNexts, hMems⟩ := hs
            subst hEnvF
            subst hNexts
            subst hMems
            -- align the tail's seed with offset off+1
            have hseed : runModule we body
                (fun td s => seedUp ((off + 1) + (k - 1 - td)) s) k
                (applyNexts st nx) (fun _ _ => 0) = some restEnvs := by
              rw [← hrest]
              exact (runModule_seed_congr we body k _ _
                (fun td htd => by
                  have h : off + (k + 1 - 1 - td)
                      = (off + 1) + (k - 1 - td) := by omega
                  simp only [h]) _ _).symm
            cases j with
            | zero => exact ⟨st, envA, rfl, hA, rfl⟩
            | succ j' =>
              have hstep' : stepModule we body (seedUp off st)
                  (fun _ _ => 0) = some (envA, nx, fun _ _ => 0) := by
                simp only [stepModule, Option.bind_eq_bind, hA, hN,
                  memNexts_memFree we body hm, Option.bind_some]
              have ih := runModule_stepIter we body hm seedUp k (off + 1)
                (applyNexts st nx) restEnvs hseed j' (by omega)
              obtain ⟨st', env1, hsi, hev, hget⟩ := ih
              refine ⟨st', env1, ?_, ?_, ?_⟩
              · rw [stepIter_succ_front we body
                  (fun t s => seedUp (off + t) s) st hstep' j']
                rw [stepIter_seed_congr we body
                  (fun t s => seedUp (off + (t + 1)) s)
                  (fun t s => seedUp ((off + 1) + t) s) _ j'
                  (fun t ht => by
                    have h : off + (t + 1) = (off + 1) + t := by omega
                    simp only [h])]
                exact hsi
              · have hidx : off + (j' + 1) = (off + 1) + j' := by omega
                rw [hidx]
                exact hev
              · simpa using hget

end Bridge

end Tools.ConeFold
