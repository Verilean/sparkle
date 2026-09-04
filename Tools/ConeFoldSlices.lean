import Tools.ConeFold
import Tools.VerifyElab

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

mutual
-- Flatten nested concats (the HList pack nests to the right); twin of
-- the shipping arm's local `let rec flatten`.
def flattenE : Expr → List Expr
  | .concat ps => flattenL ps
  | e => [e]

def flattenL : List Expr → List Expr
  | [] => []
  | a :: rest => flattenE a ++ flattenL rest
end

/-- Twin of the shipping arm's local `widthOfPart` closure. -/
def widthOfPartT (wt : Std.HashMap String Nat) : Expr → Option Nat
  | .const _ w => some w
  | .ref n => wt.get? n
  | .slice _ h l => some (h - l + 1)
  | _ => none

/-- Structural twin of the shipping arm's window-search `for` loop.
    The lists are MSB-first; `acc` is the total width of the REMAINING
    parts, so the head occupies `[acc - w, acc - 1]`. -/
def findWindow (hi lo : Nat) : List Expr → List Nat → Nat → Option Expr
  | p :: ps, w :: ws, acc =>
    if 0 < w ∧ lo ≤ hi ∧ lo = acc - w ∧ hi = acc - 1 then some p
    else if 0 < w ∧ lo ≤ hi ∧ acc - w ≤ lo ∧ hi ≤ acc - 1 then
      some (.slice p (hi - (acc - w)) (lo - (acc - w)))
    else findWindow hi lo ps ws (acc - w)
  | _, _, _ => none

mutual
/-- Total twin of the shipping `partial def resolveSlicesW`
    (Tools/VerifyElab.lean).  Fuel decreases on the self-re-entering
    calls; the expression shrinks on the rest — (fuel, e) is the
    measure, as for `inlineConeT`. -/
def resolveSlicesT (wt : Std.HashMap String Nat) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, .slice (.concat parts0) hi lo =>
    let parts := resolveSlicesTL wt fuel (flattenL parts0)
    match parts.mapM (widthOfPartT wt) with
    | none => .slice (.concat parts) hi lo
    | some ws =>
      match findWindow hi lo parts ws (ws.foldl (· + ·) 0) with
      | some r => r
      | none => .slice (.concat parts) hi lo
  | fuel + 1, .op o args => .op o (resolveSlicesTL wt fuel args)
  | fuel + 1, .concat args => .concat (resolveSlicesTL wt fuel args)
  | fuel + 1, .slice e hi lo =>
    match resolveSlicesT wt fuel e with
    | .concat parts => resolveSlicesT wt fuel (.slice (.concat parts) hi lo)
    | .ref n =>
      if lo == 0 && wt.get? n == some (hi + 1) then .ref n
      else .slice (.ref n) hi lo
    | .slice inner ihi ilo =>
      if ilo + hi ≤ ihi ∧ lo ≤ hi then
        resolveSlicesT wt fuel (.slice inner (ilo + hi) (ilo + lo))
      else .slice (.slice inner ihi ilo) hi lo
    | e' => .slice e' hi lo
  | _, e => e

def resolveSlicesTL (wt : Std.HashMap String Nat) :
    Nat → List Expr → List Expr
  | _, [] => []
  | fuel, a :: rest =>
    resolveSlicesT wt fuel a :: resolveSlicesTL wt fuel rest
end

-- Fidelity probes against the shipping function, on the shapes the
-- pack/cone pipeline actually produces.
section FidelityProbes
private def wtP : Std.HashMap String Nat :=
  (({} : Std.HashMap String Nat).insert "a" 8).insert "b" 4 |>.insert "c" 1

private def chk (e : Expr) : Bool :=
  decide (resolveSlicesT wtP 100 e = Tools.VerifyElab.resolveSlicesW wtP e)

-- exact window on a pack slice (MSB part and LSB part)
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 11 4)
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 3 0)
-- contained window inside one part
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 9 6)
-- nested concat flattening
#guard chk (.slice (.concat [.concat [.ref "c", .ref "a"], .ref "b"]) 12 4)
-- identity-slice collapse
#guard chk (.slice (.ref "a") 7 0)
-- non-identity slice stays
#guard chk (.slice (.ref "a") 6 1)
-- slice-of-slice fusion (in-range)
#guard chk (.slice (.slice (.ref "a") 6 1) 3 1)
-- recursion through ops and window falling across the general arm
#guard chk (.op .add [.slice (.concat [.ref "b", .ref "b"]) 7 4, .ref "b"])
-- straddling window: unresolved on both sides
#guard chk (.slice (.concat [.ref "a", .ref "b"]) 8 2)
end FidelityProbes

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
  rw [resolveSlicesT.eq_def]

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
  | const v w => rw [resolveSlicesT.eq_def]
  | ref n => rw [resolveSlicesT.eq_def]
  | op o args => rw [resolveSlicesT.eq_def]
  | slice i a b => rw [resolveSlicesT.eq_def]
  | sliceDim i d j => rw [resolveSlicesT.eq_def]
  | index a i => rw [resolveSlicesT.eq_def]

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

end Tools.ConeFold
