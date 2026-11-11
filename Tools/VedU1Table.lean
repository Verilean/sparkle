import Sparkle.IR.Semantics
import Sparkle.IR.ReorderInvariance
import Tools.VedU1Contract
import Std.Data.String.ToNat

/-!
# Constant-table leaves for U1 (`kLut!` mux chains), IR side

The compiler turns `kLut! i [v₀, …, v_t]` into a flat body

* for `k < t`: `_tmp_b_{3k} := const k`, `_tmp_mux_cond_{3k+1} := (i == _tmp_b_{3k})`,
  `_tmp_mux_then_{3k+2} := const vₖ`,
* `_tmp_mux_else_{3t} := const v_t`,
* then, for `j = 1 … t`, the else chain `else_{3t+j} := mux cond_k then_k else_{3t+j-1}` with
  `k = t - j` (the last one, `k = 0`, is `_gen_out`),
* `out := _gen_out`.

`tblBody` is that body.  `evalAssigns_tblBody` evaluates it ONCE, by induction on the table, to the
table lookup, so a design proof never unfolds a `t`-deep chain with `simp`: it only checks (in the
kernel, by `decide`) that the synthesized body IS `tblBody` of the table read from it.
Untrusted like the script: the kernel checks everything.
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

def entry (inp : String) (iw w k v : Nat) : List Stmt :=
  [.assign (nm 0 (3 * k)) (.const (Int.ofNat k) iw),
   .assign (nm 1 (3 * k + 1)) (.op .eq [.ref inp, .ref (nm 0 (3 * k))]),
   .assign (nm 2 (3 * k + 2)) (.const (Int.ofNat v) w)]

/-- the entries `vs` at indices `k, k+1, …` -/
def pre (inp : String) (iw w : Nat) : Nat → List Nat → List Stmt
  | _, [] => []
  | k, v :: vs => entry inp iw w k v ++ pre inp iw w (k + 1) vs

/-- wire written by else step `j` (`j = 0`: the start constant, `j = t`: `_gen_out`) -/
def tgt (t j : Nat) : String := if t - j = 0 then "_gen_out" else nm 3 (3 * t + j)

def step (t j : Nat) : Stmt :=
  .assign (tgt t j) (.op .mux [.ref (nm 1 (3 * (t - j) + 1)), .ref (nm 2 (3 * (t - j) + 2)),
    .ref (nm 3 (3 * t + j - 1))])

def chain (t : Nat) : Nat → List Stmt
  | 0 => []
  | j + 1 => chain t j ++ [step t (j + 1)]

/-- the body for entries `tbl` (indices `0 … t-1`) and the default `last` -/
def tblBody (inp : String) (iw w : Nat) (tbl : List Nat) (last : Nat) : List Stmt :=
  pre inp iw w 0 tbl ++ [.assign (nm 3 (3 * tbl.length)) (.const (Int.ofNat last) w)] ++
    chain tbl.length tbl.length ++ [.assign "out" (.ref "_gen_out")]

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

theorem nm_ne_of_get1 {inp : String} (h : inp.toList[1]? = some 'g') (a j : Nat) : nm a j ≠ inp := by
  intro e
  have := nm_get1 a j
  rw [e, h] at this
  simp at this

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

theorem evalAssigns_append (we : WEnv) (mems : MEnv) (a b : List Stmt) (env : Env) :
    evalAssigns we mems (a ++ b) env = (evalAssigns we mems a env).bind (evalAssigns we mems b) := by
  induction a generalizing env with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | assign l r =>
      simp only [List.cons_append, evalAssigns]
      cases evalExpr we env r with
      | none => rfl
      | some v => exact ih _
    | register _ _ _ _ _ => simpa only [List.cons_append, evalAssigns] using ih env
    | memory name aw dw _ _ _ _ ra rd cr _ er =>
      simp only [List.cons_append, evalAssigns]
      split
      · cases comboReads we mems name aw dw ((ra, rd) :: er) env with
        | none => rfl
        | some env' => exact ih _
      · exact ih env
    | inst _ _ _ => simpa only [List.cons_append, evalAssigns] using ih env

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

/-- the entries of `pre` evaluate to the condition / value wires, touching nothing else -/
theorem pre_eval (we : WEnv) (mems : MEnv) (inp : String) (iw w : Nat)
    (hinp : inp.toList[1]? = some 'g') :
    ∀ (vs : List Nat) (k : Nat) (env : Env), k + vs.length ≤ 2 ^ iw →
    ∃ env', evalAssigns we mems (pre inp iw w k vs) env = some env' ∧
      (∀ n, (∀ i, i < vs.length → n ≠ nm 0 (3 * (k + i)) ∧ n ≠ nm 1 (3 * (k + i) + 1) ∧
        n ≠ nm 2 (3 * (k + i) + 2)) → env' n = env n) ∧
      (∀ i, i < vs.length → env' (nm 1 (3 * (k + i) + 1)) = if env inp = k + i then 1 else 0) ∧
      (∀ i, i < vs.length → env' (nm 2 (3 * (k + i) + 2)) = vs.getD i 0 % 2 ^ w) := by
  intro vs
  induction vs with
  | nil => intro k env _; exact ⟨env, rfl, fun _ _ => rfl, fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩
  | cons v vs ih =>
    intro k env hk
    simp only [List.length_cons] at hk
    have hkw : k % 2 ^ iw = k := Nat.mod_eq_of_lt (by omega)
    have hI := nm_ne_of_get1 hinp
    have n01 : nm 0 (3 * k) ≠ nm 1 (3 * k + 1) := fun h => by have := (nm_inj (by omega) (by omega) h).1; omega
    have n02 : nm 0 (3 * k) ≠ nm 2 (3 * k + 2) := fun h => by have := (nm_inj (by omega) (by omega) h).1; omega
    have n12 : nm 1 (3 * k + 1) ≠ nm 2 (3 * k + 2) := fun h => by have := (nm_inj (by omega) (by omega) h).1; omega
    have hi1 : inp ≠ nm 0 (3 * k) := (hI 0 _).symm
    have hi2 : inp ≠ nm 1 (3 * k + 1) := (hI 1 _).symm
    have hi3 : inp ≠ nm 2 (3 * k + 2) := (hI 2 _).symm
    have hev : evalAssigns we mems (pre inp iw w k (v :: vs)) env =
        evalAssigns we mems (pre inp iw w (k + 1) vs)
          (upd (upd (upd env (nm 0 (3 * k)) k) (nm 1 (3 * k + 1))
            (if env inp = k then 1 else 0)) (nm 2 (3 * k + 2)) (v % 2 ^ w)) := by
      simp only [pre, entry, List.cons_append, List.nil_append, evalAssigns, eval_constN, eval_eq, hkw,
        Option.bind_eq_bind, Option.bind_some]
      congr 1
      funext n
      simp [upd, hi1]
    obtain ⟨env', hrun, hfr, hc, hd⟩ := ih (k + 1) _ (by omega)
    refine ⟨env', by rw [hev]; exact hrun, ?_, ?_, ?_⟩
    · intro n hn
      have h0 := hn 0 (by simp)
      rw [hfr n (fun i hi => by
        have := hn (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this)]
      simp only [Nat.add_zero] at h0
      rw [upd_ne _ _ _ h0.2.2, upd_ne _ _ _ h0.2.1, upd_ne _ _ _ h0.1]
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero]
        rw [hfr (nm 1 (3 * k + 1)) (fun i hi => by
          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
          have := nm_inj (by omega) (by omega) h <;> omega)]
        rw [upd_ne _ _ _ n12, upd_same]
      | succ i =>
        have := hc i (by simp at hi; omega)
        rw [show k + (i + 1) = k + 1 + i by omega, this]
        rw [upd_ne _ _ _ hi3.symm.symm, upd_ne _ _ _ hi2, upd_ne _ _ _ hi1]
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero]
        rw [hfr (nm 2 (3 * k + 2)) (fun i hi => by
          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
          have := nm_inj (by omega) (by omega) h <;> omega)]
        rw [upd_same]
        rfl
      | succ i =>
        have := hd i (by simp at hi; omega)
        rw [show k + (i + 1) = k + 1 + i by omega, this]
        rfl

theorem go_ne (a j : Nat) : nm a j ≠ "_gen_out" := nm_ne_of_get1 (by decide) a j

/-- a condition / value wire is never an else-chain target -/
theorem nm_ne_tgt {a : Nat} (ha : a ≤ 2) (i t j : Nat) : nm a i ≠ tgt t j := by
  unfold tgt
  split
  · exact go_ne a i
  · intro h; have := (nm_inj (by omega) (by omega) h).1; omega

/-- the else chain's value after `j` steps: the first `c i ≠ 0` from the top picks `d i` -/
def cv (c d : Nat → Nat) (t last : Nat) : Nat → Nat
  | 0 => last
  | j + 1 => if c (t - (j + 1)) ≠ 0 then d (t - (j + 1)) else cv c d t last j

theorem chain_eval (we : WEnv) (mems : MEnv) (t : Nat) (ht : 1 ≤ t) (L : Nat) :
    ∀ j, j ≤ t → ∀ env : Env, env (nm 3 (3 * t)) = L →
    ∃ env2, evalAssigns we mems (chain t j) env = some env2 ∧
      env2 (tgt t j) = cv (fun i => env (nm 1 (3 * i + 1))) (fun i => env (nm 2 (3 * i + 2))) t L j ∧
      (∀ n, (∀ j', j' ≤ j → n ≠ tgt t j') → env2 n = env n) := by
  intro j
  induction j with
  | zero =>
    intro _ env hL
    refine ⟨env, rfl, ?_, fun _ _ => rfl⟩
    have : tgt t 0 = nm 3 (3 * t) := by simp [tgt]; omega
    rw [this]; exact hL
  | succ j ih =>
    intro hj env hL
    obtain ⟨env2, hrun, hv, hfr⟩ := ih (by omega) env hL
    have hfrc : ∀ a, a ≤ 2 → ∀ i, env2 (nm a i) = env (nm a i) := fun a ha i =>
      hfr _ (fun j' _ => nm_ne_tgt ha i t j')
    have htj : tgt t j = nm 3 (3 * t + j) := by simp [tgt]; omega
    have hprev : nm 3 (3 * t + (j + 1) - 1) = tgt t j := by rw [htj]; congr 1
    refine ⟨upd env2 (tgt t (j + 1)) (if env2 (nm 1 (3 * (t - (j + 1)) + 1)) ≠ 0
        then env2 (nm 2 (3 * (t - (j + 1)) + 2)) else env2 (tgt t j)), ?_, ?_, ?_⟩
    · simp only [chain, evalAssigns_append, hrun, Option.bind_some, step, evalAssigns, eval_mux, hprev,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · rw [upd_same]
      simp only [cv, hfrc 1 (by omega), hfrc 2 (by omega), hv]
    · intro n hn
      rw [upd_ne _ _ _ (hn (j + 1) (Nat.le_refl _))]
      exact hfr n (fun j' hj' => hn j' (by omega))

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

theorem cv_congr (c d c' d' : Nat → Nat) (t L : Nat)
    (hc : ∀ i, i < t → c i = c' i) (hd : ∀ i, i < t → d i = d' i) :
    ∀ j, j ≤ t → cv c d t L j = cv c' d' t L j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    simp only [cv]
    rw [hc _ (by omega), hd _ (by omega), ih (by omega)]

/-- The whole body: `out` is the table lookup (mod `2 ^ w`) of the input's value. -/
theorem tblBody_eval (we : WEnv) (mems : MEnv) (inp : String) (iw w : Nat)
    (hinp : inp.toList[1]? = some 'g') (tbl : List Nat) (last : Nat)
    (ht : 1 ≤ tbl.length) (hlen : tbl.length ≤ 2 ^ iw) (env0 : Env) :
    ∃ envF, evalAssigns we mems (tblBody inp iw w tbl last) env0 = some envF ∧
      envF "out" = pick (env0 inp) 0 tbl last % 2 ^ w := by
  obtain ⟨env1, hpre, hfr, hc, hd⟩ := pre_eval we mems inp iw w hinp tbl 0 env0 (by omega)
  have h1 : ∀ a, a ≤ 2 → ∀ i, upd env1 (nm 3 (3 * tbl.length)) (last % 2 ^ w) (nm a i) = env1 (nm a i) :=
    fun a ha i => upd_ne _ _ _ (fun h => by have := (nm_inj (by omega) (by omega) h).1; omega)
  obtain ⟨env2, hch, hv, hf2⟩ := chain_eval we mems tbl.length ht (last % 2 ^ w) tbl.length (Nat.le_refl _)
    (upd env1 (nm 3 (3 * tbl.length)) (last % 2 ^ w)) (upd_same _ _ _)
  have htg : tgt tbl.length tbl.length = "_gen_out" := by simp [tgt]
  rw [htg] at hv
  rw [cv_congr _ _ (fun i => if env0 inp = i then 1 else 0) (fun i => tbl.getD i 0 % 2 ^ w) tbl.length _
    (fun i hi => by rw [h1 1 (by omega)]; simpa using hc i hi)
    (fun i hi => by rw [h1 2 (by omega)]; simpa using hd i hi) _ (Nat.le_refl _)] at hv
  have hcv := cv_eq tbl last (env0 inp) w tbl.length (Nat.le_refl _)
  simp only [Nat.sub_self, List.drop_zero] at hcv
  rw [hcv] at hv
  refine ⟨upd env2 "out" (env2 "_gen_out"), ?_, by rw [upd_same, hv]⟩
  have hch' : evalAssigns we mems (chain tbl.length tbl.length)
      (fun n => if n = nm 3 (3 * tbl.length) then last % 2 ^ w else env1 n) = some env2 := hch
  simp only [tblBody, List.append_assoc, evalAssigns_append, hpre, Option.bind_some, List.cons_append,
    List.nil_append, evalAssigns, eval_constN, hch', eval_ref, Option.bind_eq_bind]
  rfl

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

theorem all_pre (inp : String) (iw w : Nat) : ∀ (vs : List Nat) (k : Nat), (pre inp iw w k vs).all isAsg = true := by
  intro vs
  induction vs with
  | nil => intro _; rfl
  | cons v vs ih => intro k; simp [pre, entry, isAsg, ih]

theorem all_chain (t : Nat) : ∀ j, (chain t j).all isAsg = true := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => simp [chain, step, isAsg, List.all_append, ih]

theorem all_tblBody (inp : String) (iw w : Nat) (tbl : List Nat) (last : Nat) :
    (tblBody inp iw w tbl last).all isAsg = true := by
  simp [tblBody, isAsg, List.all_append, all_pre, all_chain]

/-- One cycle of the table body: no register update, memories unchanged, `out` the lookup. -/
theorem step_tblBody (we : WEnv) (mems : MEnv) (inp : String) (iw w : Nat)
    (hinp : inp.toList[1]? = some 'g') (tbl : List Nat) (last : Nat)
    (ht : 1 ≤ tbl.length) (hlen : tbl.length ≤ 2 ^ iw) (env0 : Env) :
    ∃ envF, stepModule we (tblBody inp iw w tbl last) env0 mems = some (envF, [], mems) ∧
      envF "out" = pick (env0 inp) 0 tbl last % 2 ^ w := by
  obtain ⟨envF, h, hout⟩ := tblBody_eval we mems inp iw w hinp tbl last ht hlen env0
  refine ⟨envF, ?_, hout⟩
  simp only [stepModule, h, regNexts_asg we mems _ _ (all_tblBody inp iw w tbl last),
    memNexts_asg we _ mems _ (all_tblBody inp iw w tbl last), Option.bind_eq_bind, Option.bind_some]

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
        simp only [beq_iff_eq, BitVec.ofNat_eq_ofNat, ne_eq]
        intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
      simp only [hne, if_false, if_neg h]
      exact ih (k + 1) last (by omega)

/-! ## Position-indexed straight-line bodies (the general route)

The compiler shares equal constants (by value and width) and refers to the first wire that holds
one, so the body of a table is not always `tblBody`: an entry equal to an index constant (the
S-box: an 8-bit index and 8-bit entries) is an alias, and a mux operand names the root wire.  What
is fixed is the wire naming: position `i` of the body defines `W i`, with `W` injective, and every
statement reads earlier positions only.  `Form` is a statement by the positions it reads. -/

inductive Form
  | const (c w : Nat)
  | alias (j : Nat)
  | eqIn (j : Nat)
  | mux (c t f : Nat)

/-- the positions a form reads -/
def Form.reads : Form → List Nat
  | .const _ _ => []
  | .alias j => [j]
  | .eqIn j => [j]
  | .mux c t f => [c, t, f]

def Form.denote (inp : String) (W : Nat → String) : Form → Expr
  | .const c w => .const (Int.ofNat c) w
  | .alias j => .ref (W j)
  | .eqIn j => .op .eq [.ref inp, .ref (W j)]
  | .mux c t f => .op .mux [.ref (W c), .ref (W t), .ref (W f)]

/-- the value of a form from the input value `x` and the values of the earlier positions -/
def Form.ev (x : Nat) (vs : List Nat) : Form → Nat
  | .const c w => c % 2 ^ w
  | .alias j => vs.getD j 0
  | .eqIn j => if x = vs.getD j 0 then 1 else 0
  | .mux c t f => if vs.getD c 0 ≠ 0 then vs.getD t 0 else vs.getD f 0

/-- the body whose statement `i` defines `W i` by form `i` -/
def bodyFrom (inp : String) (W : Nat → String) : Nat → List Form → List Stmt
  | _, [] => []
  | i, f :: fs => .assign (W i) (f.denote inp W) :: bodyFrom inp W (i + 1) fs

/-- the values at all positions, forward -/
def valsFrom (x : Nat) : List Form → List Nat → List Nat
  | [], acc => acc
  | f :: fs, acc => valsFrom x fs (acc ++ [f.ev x acc])

def vals (x : Nat) (F : List Form) : List Nat := valsFrom x F []

/-- every form reads earlier positions only -/
def ValidF : Nat → List Form → Prop
  | _, [] => True
  | i, f :: fs => (∀ j ∈ f.reads, j < i) ∧ ValidF (i + 1) fs

theorem valsFrom_length (x : Nat) : ∀ (F : List Form) (acc : List Nat),
    (valsFrom x F acc).length = acc.length + F.length := by
  intro F
  induction F with
  | nil => intro acc; simp [valsFrom]
  | cons f fs ih => intro acc; simp [valsFrom, ih]; omega

theorem valsFrom_prefix (x : Nat) : ∀ (F : List Form) (acc : List Nat) (j : Nat), j < acc.length →
    (valsFrom x F acc).getD j 0 = acc.getD j 0 := by
  intro F
  induction F with
  | nil => intro acc j _; rfl
  | cons f fs ih =>
    intro acc j hj
    simp only [valsFrom]
    rw [ih _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- evaluating the body: the wire of position `j` holds `vals`'s value `j` -/
theorem eval_bodyFrom (we : WEnv) (mems : MEnv) (inp : String) (W : Nat → String) (x M : Nat)
    (hW : ∀ a b, a < M → b < M → W a = W b → a = b) (hI : ∀ a, a < M → W a ≠ inp) :
    ∀ (F : List Form) (i : Nat) (acc : List Nat) (env : Env), ValidF i F → i + F.length ≤ M →
      acc.length = i → env inp = x → (∀ j, j < i → env (W j) = acc.getD j 0) →
    ∃ env', evalAssigns we mems (bodyFrom inp W i F) env = some env' ∧ env' inp = x ∧
      ∀ j, j < i + F.length → env' (W j) = (valsFrom x F acc).getD j 0 := by
  intro F
  induction F with
  | nil =>
    intro i acc env _ _ hl hx hj
    exact ⟨env, rfl, hx, fun j hjl => by simp only [valsFrom]; exact hj j (by simpa using hjl)⟩
  | cons f fs ih =>
    intro i acc env hv hM hl hx hj
    obtain ⟨hr, hv'⟩ := hv
    simp only [List.length_cons] at hM
    have hWi : W i ≠ inp := hI i (by omega)
    have hev : evalExpr we env (f.denote inp W) = some (f.ev x acc) := by
      cases f with
      | const c w => exact eval_constN we env c w
      | alias j =>
        have := hj j (hr j (by simp [Form.reads]))
        simp only [Form.denote, Form.ev, eval_ref, this]
      | eqIn j =>
        have := hj j (hr j (by simp [Form.reads]))
        simp only [Form.denote, Form.ev, eval_eq, this, hx]
      | mux c t f' =>
        have h1 := hj c (hr c (by simp [Form.reads]))
        have h2 := hj t (hr t (by simp [Form.reads]))
        have h3 := hj f' (hr f' (by simp [Form.reads]))
        simp only [Form.denote, Form.ev, eval_mux, h1, h2, h3]
    have hl' : (acc ++ [f.ev x acc]).length = i + 1 := by simp [hl]
    obtain ⟨env', hrun, hx', hfin⟩ := ih (i + 1) (acc ++ [f.ev x acc])
      (upd env (W i) (f.ev x acc)) hv' (by omega) hl'
      (by rw [upd_ne _ _ _ hWi.symm]; exact hx)
      (by
        intro j hjl
        by_cases hji : j = i
        · subst hji
          rw [upd_same]
          simp [List.getD_eq_getElem?_getD, hl]
        · have hjlt : j < i := by omega
          rw [upd_ne _ _ _ (fun h => hji (hW j i (by omega) (by omega) h)),
            hj j hjlt]
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < acc.length)])
    refine ⟨env', ?_, hx', ?_⟩
    · simp only [bodyFrom, evalAssigns, hev, Option.bind_eq_bind, Option.bind_some]
      exact hrun
    · intro j hjl
      simp only [List.length_cons] at hjl
      have := hfin j (by omega)
      simpa [valsFrom] using this

/-! ### order / netlist well-formedness of a position-indexed body -/

open Sparkle.IR.Reorder Tools.VedU1Contract in
theorem writesOf_bodyFrom (inp : String) (W : Nat → String) :
    ∀ (fs : List Form) (i : Nat), writesOf (bodyFrom inp W i fs) = (List.range' i fs.length).map W := by
  intro fs
  induction fs with
  | nil => intro i; simp [bodyFrom, writesOf]
  | cons f fs ih =>
    intro i
    have := ih (i + 1)
    simp only [bodyFrom, writesOf, List.flatMap_cons, stmtWrites, List.length_cons, List.range'_succ,
      List.map_cons] at this ⊢
    rw [this]; rfl

open Sparkle.IR.Reorder in
theorem refs_denote (inp : String) (W : Nat → String) (f : Form) :
    ∀ n ∈ refsOf (f.denote inp W), n = inp ∨ ∃ j ∈ f.reads, n = W j := by
  intro n hn
  cases f <;> simp_all [Form.denote, Form.reads, refsOf, refsOf.refsList]

theorem contains_false_of_not_mem {l : List String} {n : String} (h : n ∉ l) : l.contains n = false := by
  cases hc : l.contains n
  · rfl
  · exact absurd (List.contains_iff_mem.1 hc) h

theorem mem_range'_map {W : Nat → String} {i len : Nat} {n : String} :
    n ∈ (List.range' i len).map W ↔ ∃ q, i ≤ q ∧ q < i + len ∧ W q = n := by
  simp only [List.mem_map, List.mem_range']
  constructor
  · rintro ⟨q, ⟨k, hk, rfl⟩, rfl⟩; exact ⟨i + 1 * k, by omega, by omega, rfl⟩
  · rintro ⟨q, h1, h2, rfl⟩; exact ⟨q, ⟨q - i, by omega, by omega⟩, rfl⟩

open Sparkle.IR.Reorder in
theorem woCheck_bodyFrom (inp : String) (W : Nat → String) (M : Nat)
    (hW : ∀ a b, a < M → b < M → W a = W b → a = b) (hI : ∀ a, a < M → W a ≠ inp) :
    ∀ (fs : List Form) (i : Nat), ValidF i fs → i + fs.length ≤ M →
      woCheck ((List.range i).map W) (bodyFrom inp W i fs) = true := by
  intro fs
  induction fs with
  | nil => intro i _ _; simp [bodyFrom, woCheck]
  | cons f fs ih =>
    intro i hv hM
    obtain ⟨hr, hv'⟩ := hv
    simp only [List.length_cons] at hM
    simp only [bodyFrom, woCheck, stmtReads, stmtWrites, writesOf_bodyFrom, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', List.mem_singleton, forall_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro n hn
      have hn' := refs_denote inp W f n hn
      apply contains_false_of_not_mem
      intro hmem
      obtain ⟨q, hq1, hq2, hq⟩ := mem_range'_map.1 hmem
      rcases hn' with rfl | ⟨j, hj, rfl⟩
      · exact hI q (by omega) hq
      · have := hW q j (by omega) (by have := hr j hj; omega) hq
        have := hr j hj
        omega
    · refine ⟨contains_false_of_not_mem ?_, contains_false_of_not_mem ?_⟩
      · intro hmem
        obtain ⟨q, hq1, hq2⟩ := List.mem_map.1 hmem
        have hq1' := List.mem_range.1 hq1
        have := hW q i (by omega) (by omega) hq2
        omega
      · intro hmem
        obtain ⟨q, hq1, hq2, hq⟩ := mem_range'_map.1 hmem
        have := hW q i (by omega) (by omega) hq
        omega
    · have := ih (i + 1) hv' (by omega)
      have e : (List.range i).map W ++ [W i] = (List.range (i + 1)).map W := by
        rw [List.range_succ, List.map_append]; rfl
      rw [e]; exact this

theorem mem_bodyFrom (inp : String) (W : Nat → String) :
    ∀ (fs : List Form) (i : Nat), ValidF i fs → ∀ s ∈ bodyFrom inp W i fs,
      ∃ (f : Form) (p : Nat), i ≤ p ∧ p < i + fs.length ∧ s = .assign (W p) (f.denote inp W) ∧ ∀ j ∈ f.reads, j < p := by
  intro fs
  induction fs with
  | nil => intro i _ s hs; simp [bodyFrom] at hs
  | cons f fs ih =>
    intro i hv s hs
    obtain ⟨hr, hv'⟩ := hv
    simp only [bodyFrom, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨f, i, Nat.le_refl _, by simp, rfl, hr⟩
    · obtain ⟨f', p, h1, h2, h3, h4⟩ := ih (i + 1) hv' s hs
      exact ⟨f', p, by omega, by simp; omega, h3, h4⟩

theorem isPermOf_refl_aux {α : Type} [DecidableEq α] : ∀ (l : List α), Sparkle.IR.Reorder.isPermOf l l = true := by
  intro l
  induction l with
  | nil => rfl
  | cons a rest ih => simp [Sparkle.IR.Reorder.isPermOf, ih]

open Sparkle.IR.Reorder Tools.VedU1Contract in
theorem regsOf_bodyFrom (inp : String) (W : Nat → String) :
    ∀ (fs : List Form) (i : Nat), regsOf (bodyFrom inp W i fs) = [] := by
  intro fs
  induction fs with
  | nil => intro i; rfl
  | cons f fs ih => intro i; simp [bodyFrom, regsOf, ih]

open Sparkle.IR.Reorder in
theorem nextKeys_bodyFrom (inp : String) (W : Nat → String) :
    ∀ (fs : List Form) (i : Nat), nextKeys (bodyFrom inp W i fs) = [] := by
  intro fs
  induction fs with
  | nil => intro i; rfl
  | cons f fs ih => intro i; simp [bodyFrom, nextKeys, List.flatMap_cons] at ih ⊢; exact ih _

open Sparkle.IR.Reorder in
theorem memNames_bodyFrom (inp : String) (W : Nat → String) :
    ∀ (fs : List Form) (i : Nat), (bodyFrom inp W i fs).filterMap stmtMemName = [] := by
  intro fs
  induction fs with
  | nil => intro i; rfl
  | cons f fs ih => intro i; simp [bodyFrom, List.filterMap_cons, stmtMemName, ih]

theorem bnot_contains {l : List String} {n : String} : ((!l.contains n) = true) ↔ n ∉ l := by
  rw [Bool.not_eq_true']
  constructor
  · intro h hm
    rw [List.contains_iff_mem.2 hm] at h
    cases h
  · exact contains_false_of_not_mem

open Sparkle.IR.Reorder Tools.VedU1Contract in
/-- A position-indexed body is a well-ordered netlist (`OrderOk`): no `O(n²)` string scan. -/
theorem orderOk_bodyFrom (m : Sparkle.IR.AST.Module) (inp : String) (W : Nat → String) (F : List Form)
    (hv : ValidF 0 F) (hW : ∀ a b, a < F.length → b < F.length → W a = W b → a = b)
    (hI : ∀ a, a < F.length → W a ≠ inp) (hbody : m.body = bodyFrom inp W 0 F)
    (hin : m.inputs.map (·.name) = [inp]) (hout : ∀ p ∈ m.outputs, ∃ q, q < F.length ∧ p.name = W q) :
    OrderOk m (bodyFrom inp W 0 F) = true := by
  have hw := writesOf_bodyFrom inp W F 0
  have hall := mem_bodyFrom inp W F 0 hv
  unfold OrderOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bnot_contains, List.contains_iff_mem,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← hbody]; exact isPermOf_refl_aux _
  · exact woCheck_bodyFrom inp W F.length hW hI F 0 hv (by simp)
  · rw [nextKeys_bodyFrom]; exact List.nodup_nil
  · rw [memNames_bodyFrom]; exact List.nodup_nil
  · intro s hs n hn
    obtain ⟨f, p, h1, h2, rfl, h4⟩ := hall s hs
    simp only [stmtReads, stmtWrites, List.mem_singleton] at hn ⊢
    rcases refs_denote inp W f n hn with rfl | ⟨j, hj, rfl⟩
    · exact fun h => hI p (by omega) h.symm
    · exact fun h => by
        have := hW j p (by have := h4 j hj; omega) (by omega) h
        have := h4 j hj; omega
  · intro s hs n hn
    obtain ⟨f, p, h1, h2, rfl, h4⟩ := hall s hs
    simp only [allReads, stmtReads] at hn ⊢
    rw [hw, regsOf_bodyFrom]
    rcases refs_denote inp W f n hn with rfl | ⟨j, hj, rfl⟩
    · left; left; rw [hin]; simp
    · right; exact mem_range'_map.2 ⟨j, by omega, by have := h4 j hj; omega, rfl⟩
  · intro p hp
    obtain ⟨q, hq, hn⟩ := hout p hp
    rw [hw, regsOf_bodyFrom]
    right
    exact mem_range'_map.2 ⟨q, by omega, by omega, hn.symm⟩
  · intro n hn
    rw [hw] at hn
    obtain ⟨q, _, hq, rfl⟩ := mem_range'_map.1 hn
    rw [regsOf_bodyFrom]
    refine ⟨?_, by simp⟩
    rw [hin]
    simp only [List.mem_singleton]
    exact fun h => hI q (by omega) h
  · intro n hn
    rw [regsOf_bodyFrom] at hn
    simp at hn

end Tools.VedU1Table
