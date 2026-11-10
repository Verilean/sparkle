import Sparkle.IR.ReorderInvariance
import Sparkle.IR.Semantics

/-!
# Per-statement evaluation of an assign-only body (`Tools.VedU1Script`)

The flat `simp [stepModule, evalAssigns, …]` of the first U1 script rewrites the
whole body in one term: the `Option.bind` chain, the `Env` update chain and the
operand values all nest as deep as the body is long.  This file proves, once,
the facts the generated proof needs instead, so a body of `n` statements costs
`n` small steps and no deep term:

* `evalExpr_isSome_env`: `evalExpr` fails on the SHAPE of an expression only,
  never on the environment;
* `evalAssigns_fix`: for a well-ordered body of assignments (and registers,
  which the combinational fold skips) in which no statement reads its own
  target and every expression has a value, `evalAssigns` succeeds, and the
  environment `E` it returns satisfies ONE equation per statement
  `evalExpr we E r = some (E l)` over that same `E`, and agrees with the seed
  on every name the body does not write.
-/

namespace Tools.VedU1Script

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder

/-! ## `evalExpr` fails on shape only -/

theorem evalList_length (we : WEnv) (env : Env) :
    ∀ (args : List Expr) (vs : List Nat), evalList we env args = some vs → vs.length = args.length := by
  intro args
  induction args with
  | nil => intro vs h; simp [evalList] at h; subst h; rfl
  | cons a rest ih =>
    intro vs h
    simp only [evalList] at h
    cases hv : evalExpr we env a with
    | none => simp [hv] at h
    | some v =>
      cases hr : evalList we env rest with
      | none => simp [hv, hr] at h
      | some vs' =>
        simp [hv, hr] at h
        subst h
        simp [ih _ hr]

theorem evalOp_isSome_len (we : WEnv) (op : Operator) (args : List Expr) (vs vs' : List Nat)
    (w w' : Nat) (h : vs.length = vs'.length) :
    (evalOp we op args vs w).isSome = (evalOp we op args vs' w').isSome := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, vs⟩⟩⟩⟩ <;>
  rcases vs' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨d', vs'⟩⟩⟩⟩ <;>
  all_goals (try (simp at h; done))
  all_goals (cases op <;> rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, args⟩⟩⟩ <;> simp [evalOp])

mutual
theorem evalExpr_isSome_env (we : WEnv) (env env' : Env) :
    ∀ e : Expr, (evalExpr we env e).isSome = (evalExpr we env' e).isSome
  | .const _ _ => rfl
  | .ref _ => rfl
  | .op o args => by
    have ih := evalList_isSome_env we env env' args
    simp only [evalExpr]
    cases h1 : evalList we env args with
    | none =>
      rw [h1] at ih
      cases h2 : evalList we env' args with
      | none => rfl
      | some _ => rw [h2] at ih; simp at ih
    | some vs =>
      rw [h1] at ih
      cases h2 : evalList we env' args with
      | none => rw [h2] at ih; simp at ih
      | some vs' =>
        exact evalOp_isSome_len we o args vs vs' _ _
          (by rw [evalList_length we env args vs h1, evalList_length we env' args vs' h2])
  | .concat args => by
    have ih := evalList_isSome_env we env env' args
    simp only [evalExpr]
    cases h1 : evalList we env args with
    | none =>
      rw [h1] at ih
      cases h2 : evalList we env' args with
      | none => rfl
      | some _ => rw [h2] at ih; simp at ih
    | some vs =>
      rw [h1] at ih
      cases h2 : evalList we env' args with
      | none => rw [h2] at ih; simp at ih
      | some vs' => rfl
  | .slice e hi lo => by
    have ih := evalExpr_isSome_env we env env' e
    simp only [evalExpr]
    cases h1 : evalExpr we env e with
    | none =>
      rw [h1] at ih
      cases h2 : evalExpr we env' e with
      | none => rfl
      | some _ => rw [h2] at ih; simp at ih
    | some v =>
      rw [h1] at ih
      cases h2 : evalExpr we env' e with
      | none => rw [h2] at ih; simp at ih
      | some v' => rfl
  | .sliceDim _ _ _ => rfl
  | .index _ _ => rfl

theorem evalList_isSome_env (we : WEnv) (env env' : Env) :
    ∀ args : List Expr, (evalList we env args).isSome = (evalList we env' args).isSome
  | [] => rfl
  | a :: rest => by
    have ih1 := evalExpr_isSome_env we env env' a
    have ih2 := evalList_isSome_env we env env' rest
    simp only [evalList]
    cases h1 : evalExpr we env a <;> cases h2 : evalExpr we env' a <;>
      cases h3 : evalList we env rest <;> cases h4 : evalList we env' rest <;>
      simp_all
end

/-! ## The final environment of an assign-only body -/

/-- Checked by the kernel for a concrete body: assignments (every expression has
a value, none reads its own target) and registers only. -/
def bodyOk (we : WEnv) : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (evalExpr we (fun _ => 0) r).isSome && !(refsOf r).contains l && bodyOk we rest
  | .register _ _ _ _ _ :: rest => bodyOk we rest
  | _ => false

/-- Update of one name (what `evalAssigns` does to its environment). -/
theorem evalAssigns_fix (we : WEnv) (mems : MEnv) :
    ∀ (B : List Stmt) (done : List String) (env0 : Env), WO done B → bodyOk we B = true →
      ∃ E, evalAssigns we mems B env0 = some E ∧ (∀ n, n ∉ writesOf B → E n = env0 n) ∧
        ∀ l r, Stmt.assign l r ∈ B → evalExpr we E r = some (E l) := by
  intro B
  induction B with
  | nil =>
    intro done env0 _ _
    exact ⟨env0, rfl, fun n _ => rfl, fun l r h => absurd h (by simp)⟩
  | cons s rest ih =>
    intro done env0 hwo hok
    cases hwo with
    | cons _ hreads hw hrest =>
      cases s with
      | assign l r =>
        simp only [bodyOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
        obtain ⟨⟨hsome, hself⟩, hrestok⟩ := hok
        have hsome' : (evalExpr we env0 r).isSome = true := by
          rw [← evalExpr_isSome_env we (fun _ => 0) env0 r]; exact hsome
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome'
        obtain ⟨E, hE, hframe, hfix⟩ := ih _ (fun n => if n = l then v else env0 n) hrest hrestok
        refine ⟨E, ?_, ?_, ?_⟩
        · simp only [evalAssigns, hv, Option.bind_some]; exact hE
        · intro n hn
          simp only [writesOf, List.flatMap_cons, List.mem_append, not_or] at hn
          have hn1 : n ∉ writesOf rest := hn.2
          have hnl : n ≠ l := by simpa [stmtWrites] using hn.1
          rw [hframe n hn1]; simp [hnl]
        · intro l' r' hmem
          rcases List.mem_cons.mp hmem with h | h
          · injection h with h1 h2
            subst h1; subst h2
            have hlr : l' ∉ writesOf rest := (hw l' (by simp [stmtWrites])).2
            have e1 : E l' = v := by rw [hframe l' hlr]; simp
            have hag : ∀ n ∈ refsOf r', env0 n = E n := by
              intro n hn
              have hnw : n ∉ writesOf rest := hreads n (by simpa [stmtReads] using hn)
              have hnl : n ≠ l' := by
                intro h; subst h; simp at hself; exact hself hn
              rw [hframe n hnw]; simp [hnl]
            rw [e1, ← evalExpr_congr we env0 E r' hag]; exact hv
          · exact hfix l' r' h
      | register o c rr e i =>
        simp only [bodyOk] at hok
        obtain ⟨E, hE, hframe, hfix⟩ := ih _ env0 hrest hok
        refine ⟨E, ?_, ?_, ?_⟩
        · simpa [evalAssigns] using hE
        · intro n hn
          exact hframe n (by simpa [writesOf, stmtWrites] using hn)
        · intro l' r' hmem
          rcases List.mem_cons.mp hmem with h | h
          · cases h
          · exact hfix l' r' h
      | _ => simp [bodyOk] at hok

/-- Assignments only. -/
def allAssign : List Stmt → Bool
  | [] => true
  | .assign _ _ :: rest => allAssign rest
  | _ => false

theorem regNexts_assigns (we : WEnv) (mems : MEnv) (env : Env) :
    ∀ B : List Stmt, allAssign B = true → regNexts we mems B env = some [] := by
  intro B
  induction B with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s with
    | assign l r => simp only [allAssign] at h; simp only [regNexts]; exact ih h
    | _ => simp [allAssign] at h

theorem memNexts_assigns (we : WEnv) (mems : MEnv) (env : Env) :
    ∀ B : List Stmt, allAssign B = true → memNexts we B mems env = some mems := by
  intro B
  induction B with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s with
    | assign l r => simp only [allAssign] at h; simp only [memNexts]; exact ih h
    | _ => simp [allAssign] at h

/-- One cycle of a register-free body of assignments: the environment `E` after it
satisfies one equation per statement and keeps every name the body does not write. -/
theorem step_assigns (we : WEnv) (mems : MEnv) (B : List Stmt) (env0 : Env)
    (hwo : woCheck [] B = true) (hok : bodyOk we B = true) (hall : allAssign B = true) :
    ∃ E, stepModule we B env0 mems = some (E, [], mems) ∧ (∀ n, n ∉ writesOf B → E n = env0 n) ∧
      ∀ l r, Stmt.assign l r ∈ B → evalExpr we E r = some (E l) := by
  obtain ⟨E, hE, hf, hx⟩ := evalAssigns_fix we mems B [] env0 (woCheck_sound _ _ hwo) hok
  refine ⟨E, ?_, hf, hx⟩
  simp [stepModule, hE, regNexts_assigns we mems E B hall, memNexts_assigns we mems E B hall]


end Tools.VedU1Script
