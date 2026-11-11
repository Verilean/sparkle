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

end Tools.VedU1Table
