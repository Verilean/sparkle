import Sparkle.IR.ReorderInvariance
import Sparkle.IR.Semantics
import Tools.VedU1Lemmas
import Tools.VedU1Contract

/-!
# Multi-register step lemma for the U1 script (`Tools.VedU1ScriptSeq`)

The flat `simp [stepModule, evalAssigns, regNexts, …]` of the loop script rewrites the whole body
in one term.  This file proves, once, what the generated proof uses instead:

* `step_seq`: for a well-ordered body of assignments and registers in which every expression has
  a value, `stepModule` succeeds; the environment `E` it returns satisfies ONE equation per
  assignment (`evalExpr we E r = some (E l)`, over that same `E`), agrees with the seed on every
  name the body does not write, and the register updates are the pure list `nextsOf we E B`;
* `applyNexts_nextsOf`: the new value of one register from that list (`regOf`: the first register
  statement with that output).

Nothing here is trusted beyond the kernel: the generated script only chooses which of these
lemmas to apply.
-/

namespace Tools.VedU1ScriptSeq

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


/-! ## The final environment of an assign/register body -/

/-- Checked by the kernel for a concrete body: assignments (every expression has a value, none
reads its own target) and registers (the input expression has a value), nothing else. -/
def bodySeqOk (we : WEnv) : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (evalExpr we (fun _ => 0) r).isSome && !(refsOf r).contains l && bodySeqOk we rest
  | .register _ _ _ e _ :: rest =>
    (evalExpr we (fun _ => 0) e).isSome && bodySeqOk we rest
  | _ => false

/-- The register updates of `regNexts`, as a pure list. -/
def nextsOf (we : WEnv) (E : Env) : List Stmt → List (String × Nat)
  | [] => []
  | .register out _ (rst, _) input init :: rest =>
    (out, if E rst ≠ 0 then encodeInit init (we out) else mask (we out) ((evalExpr we E input).getD 0))
      :: nextsOf we E rest
  | _ :: rest => nextsOf we E rest

/-- The first register statement with output `n`: (reset name, input, init). -/
def regOf : List Stmt → String → Option (String × Expr × Int)
  | [], _ => none
  | .register out _ (rst, _) input init :: rest, n =>
    if out = n then some (rst, input, init) else regOf rest n
  | _ :: rest, n => regOf rest n

theorem evalAssigns_fix (we : WEnv) (mems : MEnv) :
    ∀ (B : List Stmt) (done : List String) (env0 : Env), WO done B → bodySeqOk we B = true →
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
        simp only [bodySeqOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
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
        simp only [bodySeqOk, Bool.and_eq_true] at hok
        obtain ⟨E, hE, hframe, hfix⟩ := ih _ env0 hrest hok.2
        refine ⟨E, ?_, ?_, ?_⟩
        · simpa [evalAssigns] using hE
        · intro n hn
          exact hframe n (by simpa [writesOf, stmtWrites] using hn)
        · intro l' r' hmem
          rcases List.mem_cons.mp hmem with h | h
          · cases h
          · exact hfix l' r' h
      | _ => simp [bodySeqOk] at hok

theorem regNexts_seq (we : WEnv) (mems : MEnv) (E : Env) :
    ∀ B : List Stmt, bodySeqOk we B = true → regNexts we mems B E = some (nextsOf we E B) := by
  intro B
  induction B with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s with
    | assign l r =>
      simp only [bodySeqOk, Bool.and_eq_true] at h
      simp only [regNexts, nextsOf]; exact ih h.2
    | register o c rr e i =>
      simp only [bodySeqOk, Bool.and_eq_true] at h
      have hs : (evalExpr we E e).isSome = true := by
        rw [← evalExpr_isSome_env we (fun _ => 0) E e]; exact h.1
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      simp only [regNexts, nextsOf, hv, ih h.2, Option.getD_some]
      rfl
    | _ => simp [bodySeqOk] at h

theorem memNexts_seq (we : WEnv) (mems : MEnv) (E : Env) :
    ∀ B : List Stmt, bodySeqOk we B = true → memNexts we B mems E = some mems := by
  intro B
  induction B with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s with
    | assign l r =>
      simp only [bodySeqOk, Bool.and_eq_true] at h
      simp only [memNexts]; exact ih h.2
    | register o c rr e i =>
      simp only [bodySeqOk, Bool.and_eq_true] at h
      simp only [memNexts]; exact ih h.2
    | _ => simp [bodySeqOk] at h

/-- One equation per assignment, as a conjunction over the body (statement `i` is the `i`-th
conjunct). -/
def stmtEq (we : WEnv) (E : Env) : Stmt → Prop
  | .assign l r => some (E l) = evalExpr we E r
  | _ => True

def AllP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: as => P a ∧ AllP P as

theorem allP_of_mem {α : Type} (P : α → Prop) :
    ∀ B : List α, (∀ s, s ∈ B → P s) → AllP P B
  | [], _ => trivial
  | a :: as, h => ⟨h a (List.mem_cons_self ..), allP_of_mem P as (fun s hs => h s (List.mem_cons_of_mem _ hs))⟩

/-- One cycle of a body of assignments and registers. -/
theorem step_seq (we : WEnv) (mems : MEnv) (B : List Stmt) (env0 : Env)
    (hwo : woCheck [] B = true) (hok : bodySeqOk we B = true) :
    ∃ E, stepModule we B env0 mems = some (E, nextsOf we E B, mems) ∧
      (∀ n, n ∉ writesOf B → E n = env0 n) ∧ AllP (stmtEq we E) B := by
  obtain ⟨E, hE, hf, hx⟩ := evalAssigns_fix we mems B [] env0 (woCheck_sound _ _ hwo) hok
  refine ⟨E, ?_, hf, allP_of_mem _ B ?_⟩
  · simp [stepModule, hE, regNexts_seq we mems E B hok, memNexts_seq we mems E B hok]
  · intro s hs
    cases s with
    | assign l r => exact (hx l r hs).symm
    | _ => trivial

/-- The new value of a register (the first register statement with that output), or the old
state. -/
theorem applyNexts_nextsOf (we : WEnv) (E : Env) (st : String → Nat) :
    ∀ (B : List Stmt) (n : String), applyNexts st (nextsOf we E B) n =
      match regOf B n with
      | none => st n
      | some (rst, inp, init) =>
        if E rst ≠ 0 then encodeInit init (we n) else mask (we n) ((evalExpr we E inp).getD 0) := by
  intro B n
  induction B with
  | nil => simp [applyNexts, nextsOf, regOf]
  | cons s rest ih =>
    cases s with
    | register out c rr e i =>
      by_cases h : out = n
      · subst h; simp [applyNexts, nextsOf, regOf]
      · simp only [nextsOf, regOf, h, if_false]
        rw [← ih]
        simp [applyNexts, List.find?_cons, h]
    | assign l r => simpa [nextsOf, regOf] using ih
    | _ => simpa [nextsOf, regOf] using ih

/-! ## The seed -/

theorem seedIn_input (m : Module) (ins : Nat → String → Nat) (s : Nat) (st : String → Nat) (n : String)
    (h : (m.inputs.map (·.name)).contains n = true) : Tools.VedU1Contract.seedIn m ins s st n = ins s n := by
  unfold Tools.VedU1Contract.seedIn; rw [if_pos h]

theorem seedIn_state (m : Module) (ins : Nat → String → Nat) (s : Nat) (st : String → Nat) (n : String)
    (h : (m.inputs.map (·.name)).contains n = false) : Tools.VedU1Contract.seedIn m ins s st n = st n := by
  unfold Tools.VedU1Contract.seedIn; rw [h]; rfl

/-- The range fact of the `i`-th data input (the contract's own list), by name. -/
theorem inputsOk_nth (c : Tools.VedU1Contract.Contract) (m : Module) (ins : Nat → String → Nat)
    (hok : Tools.VedU1Contract.InputsOk c m ins) (s i : Nat) (n : String)
    (h : (c.dataInputs.map (·.name))[i]? = some n) :
    ins s n < 2 ^ Tools.VedU1Contract.declWidth m n := by
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact hok.1 s a (List.mem_of_getElem? ha)

/-- `x <<< 0 = x`, with a proof that is not `rfl` (`Nat.shiftLeft_zero` is: a `rfl` lemma is used by
`simp` WITHOUT a proof, and the kernel then has to check `x <<< 0 ≡ x` by evaluation — for symbolic
`x` with big literals inside, it unfolds `Nat.mul` by recursion on the literal). -/
theorem shl_zero' (x : Nat) : x <<< 0 = x := by
  rw [Nat.shiftLeft_eq, Nat.pow_zero, Nat.mul_one]

end Tools.VedU1ScriptSeq
