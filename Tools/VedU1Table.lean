import Sparkle.IR.Semantics
import Sparkle.IR.ReorderInvariance
import Tools.VedU1Contract
import Std.Data.String.ToNat

/-!
# Constant-table leaves for U1 (`kLut!` mux chains): names, lookup, Signal side

The compiler turns `kLut! i [v₀, …, v_t]` into a flat body of temp wires `_tmp_b_{j}`,
`_tmp_mux_cond_{j}`, `_tmp_mux_then_{j}`, `_tmp_mux_else_{j}` (one global counter `j`), then
`_gen_out` and `out`.  This file has the pieces the position-indexed table route
(Tools/VedU1TableGen.lean) is built from: the wire names and their distinctness (`nm`, `nm_inj`),
the one-statement evaluation lemmas, the lookup function `pick` and the chain value `cv`
(`cv_eq`), the register-free step (`regNexts_asg`, `memNexts_asg`), and the Signal side (`lutBV`,
`lutBV_toNat`: the value of the declaration's mux chain).  Untrusted like the script: the kernel
checks everything.
-/

namespace Tools.VedU1Table

open Sparkle.IR.AST Sparkle.IR.Semantics

/-- the compiler's temp-wire prefixes: 0 `b`, 1 `cond`, 2 `then`, 3 `else` -/
def pfx : Nat → String
  | 0 => "_tmp_b_"
  | 1 => "_tmp_mux_cond_"
  | 2 => "_tmp_mux_then_"
  | _ => "_tmp_mux_else_"

/-- temp wire of kind `a` with counter `j` -/
def nm (a j : Nat) : String := pfx a ++ Nat.repr j

/-- the lookup: the first `k + i` equal to `x` selects `vs[i]`, else `last` -/
def pick (x : Nat) : Nat → List Nat → Nat → Nat
  | _, [], last => last
  | k, v :: vs, last => if x = k then v else pick x (k + 1) vs last

/-! ## the names -/

theorem pfx0 : (pfx 0).toList = ['_', 't', 'm', 'p', '_', 'b', '_'] := by decide
theorem pfx1 : (pfx 1).toList = ['_', 't', 'm', 'p', '_', 'm', 'u', 'x', '_', 'c', 'o', 'n', 'd', '_'] := by decide
theorem pfx2 : (pfx 2).toList = ['_', 't', 'm', 'p', '_', 'm', 'u', 'x', '_', 't', 'h', 'e', 'n', '_'] := by decide
theorem pfx3 : (pfx 3).toList = ['_', 't', 'm', 'p', '_', 'm', 'u', 'x', '_', 'e', 'l', 's', 'e', '_'] := by decide

theorem nm_list (a j : Nat) : (nm a j).toList = (pfx a).toList ++ (Nat.repr j).toList := by
  simp [nm]

theorem nm_get1 (a j : Nat) : (nm a j).toList[1]? = some 't' := by
  rw [nm_list]
  rcases a with _ | _ | _ | a
  · rw [pfx0]; rfl
  · rw [pfx1]; rfl
  · rw [pfx2]; rfl
  · have : pfx (a + 3) = pfx 3 := rfl
    rw [this, pfx3]; rfl

theorem nm_inj {a b j j' : Nat} (ha : a ≤ 3) (hb : b ≤ 3) (h : nm a j = nm b j') :
    a = b ∧ j = j' := by
  have hd : (pfx a).toList ++ (Nat.repr j).toList = (pfx b).toList ++ (Nat.repr j').toList := by
    rw [← nm_list, ← nm_list, h]
  have key : a = b := by
    refine Classical.byContradiction fun hab => ?_
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    first
    | exact hab rfl
    | (have e5 := congrArg (fun l => l[5]?) hd
       have e9 := congrArg (fun l => l[9]?) hd
       simp [pfx0, pfx1, pfx2, pfx3] at e5 e9)
  subst key
  have := List.append_cancel_left hd
  have h2 : Nat.repr j = Nat.repr j' := String.ext this
  exact ⟨rfl, Nat.repr_injective h2⟩

/-! ## evaluation -/

theorem eval_constN (we : WEnv) (env : Env) (v w : Nat) :
    evalExpr we env (.const (Int.ofNat v) w) = some (v % 2 ^ w) := by
  have h : (((Int.ofNat v) % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int)
      = ((v % 2 ^ w : Nat) : Int) := by
    have h1 := Int.add_mul_emod_self_right ((Int.ofNat v) % ((2 ^ w : Nat) : Int)) 1 ((2 ^ w : Nat) : Int)
    rw [Int.one_mul] at h1
    rw [h1, Int.emod_emod]
    rfl
  simp only [evalExpr, h, Int.toNat_natCast, mask]
  rw [Nat.mod_mod]

theorem eval_eq (we : WEnv) (env : Env) (a b : String) :
    evalExpr we env (.op .eq [.ref a, .ref b]) = some (if env a = env b then 1 else 0) := by
  simp [evalExpr, evalList, evalOp]

theorem eval_mux (we : WEnv) (env : Env) (c t f : String) :
    evalExpr we env (.op .mux [.ref c, .ref t, .ref f]) = some (if env c ≠ 0 then env t else env f) := by
  simp [evalExpr, evalList, evalOp]

theorem eval_ref (we : WEnv) (env : Env) (a : String) : evalExpr we env (.ref a) = some (env a) := rfl

/-- environment update (what `evalAssigns` does at an `assign`) -/
def upd (env : Env) (l : String) (v : Nat) : Env := fun n => if n = l then v else env n

theorem upd_same (env : Env) (l : String) (v : Nat) : upd env l v l = v := by simp [upd]
theorem upd_ne (env : Env) (l : String) (v : Nat) {n : String} (h : n ≠ l) : upd env l v n = env n := by
  simp [upd, h]

/-- the else chain's value after `j` steps: the first `c i ≠ 0` from the top picks `d i` -/
def cv (c d : Nat → Nat) (t last : Nat) : Nat → Nat
  | 0 => last
  | j + 1 => if c (t - (j + 1)) ≠ 0 then d (t - (j + 1)) else cv c d t last j

/-- the lookup the chain computes -/
theorem cv_eq (tbl : List Nat) (last x w : Nat) :
    ∀ j, j ≤ tbl.length →
    cv (fun i => if x = i then 1 else 0) (fun i => tbl.getD i 0 % 2 ^ w) tbl.length (last % 2 ^ w) j =
      pick x (tbl.length - j) (tbl.drop (tbl.length - j)) last % 2 ^ w := by
  intro j
  induction j with
  | zero => intro _; simp [cv, pick]
  | succ j ih =>
    intro hj
    have hk : tbl.length - (j + 1) < tbl.length := by omega
    have hk1 : tbl.length - (j + 1) + 1 = tbl.length - j := by omega
    rw [List.drop_eq_getElem_cons hk]
    simp only [cv, pick, hk1]
    rw [ih (by omega)]
    by_cases hx : x = tbl.length - (j + 1)
    · simp [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    · simp [hx]

/-! ## the step: no registers, no memories -/

def isAsg : Stmt → Bool
  | .assign _ _ => true
  | _ => false

theorem regNexts_asg (we : WEnv) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env), b.all isAsg = true → regNexts we mems b env = some [] := by
  intro b
  induction b with
  | nil => intro _ _; rfl
  | cons s rest ih =>
    intro env h
    cases s <;> simp_all [isAsg, regNexts]

theorem memNexts_asg (we : WEnv) :
    ∀ (b : List Stmt) (mems : MEnv) (env : Env), b.all isAsg = true → memNexts we b mems env = some mems := by
  intro b
  induction b with
  | nil => intro _ _ _; rfl
  | cons s rest ih =>
    intro mems env h
    cases s <;> simp_all [isAsg, memNexts]

/-! ## the Signal side -/

/-- the value of the `kLut!` chain `mux (sel == k) vₖ (…)` at a selector value `x` -/
def lutBV (iw w : Nat) (x : BitVec iw) : Nat → List Nat → Nat → BitVec w
  | _, [], last => BitVec.ofNat w last
  | k, v :: vs, last => if x == BitVec.ofNat iw k then BitVec.ofNat w v else lutBV iw w x (k + 1) vs last

theorem lutBV_toNat (iw w x : Nat) (hx : x < 2 ^ iw) :
    ∀ (vs : List Nat) (k : Nat) (last : Nat), k + vs.length ≤ 2 ^ iw →
    (lutBV iw w (BitVec.ofNat iw x) k vs last).toNat = pick x k vs last % 2 ^ w := by
  intro vs
  induction vs with
  | nil => intro k last _; simp [lutBV, pick]
  | cons v vs ih =>
    intro k last hk
    simp only [List.length_cons] at hk
    simp only [lutBV, pick]
    by_cases h : x = k
    · subst h; simp
    · have hne : ¬ (BitVec.ofNat iw x == BitVec.ofNat iw k) = true := by
        simp only [beq_iff_eq]
        intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
      simp only [hne, if_neg h]
      exact ih (k + 1) last (by omega)

end Tools.VedU1Table
