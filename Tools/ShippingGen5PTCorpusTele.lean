import Tools.ShippingGen5PTCorpusSpec
set_option autoImplicit false
/-! # `RowTeleEvAt PTcorpus` for the rows whose binder types mention the earlier type arguments (issue sparkle-ledger-dd4-deprows, Q-C 2nd step; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Tele)

No TRUSTED, axiom, `sorry`, `native_decide`. Existing files are unchanged. A row is counted only when a theorem `RowTeleEvAt PTcorpus env c ls` exists; its env facts stay hypotheses (`EnvForms`, `¬ IsDefn env D`, `EnvClosedL env`), evaluated in the real environment by `Tests/Gen5/PTCorpusTeleCheck.lean`.

* §1 `Form`: the binder types that occur (a type argument, a closed type constant, a one-argument type former, an arrow). `FE es i j F` is the expression that the binder `j` carries after the first `i` binders were replaced by `es`.
  `post_subst` is the computation of `substS` on a whole telescope (the step `TeleEv.tm` / `TeleEv.ty` take); `tdenF` derives `TDenV` of such a binder from the denotations of the substituted arguments (`tdenv_wk` under `EnvClosedL` for the lifts).
* §2 `teleEv_forms` / `rowTeleEvAt_of_forms`: `RowTeleEvAt` from the row's argument types (`FormsAre`, by construction of the telescope) and the env fact `EnvForms`. -/
namespace Tools.ShippingGen5PTCorpusTele
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV Tools.ShippingGen5PTCorpus

/-! ## §1 Binder forms -/

/-- The binder types of the open rows, over the earlier TYPE arguments (`var p` = the argument of binder `p`). -/
inductive Form : Type 1
  | var (p : Nat)
  | cst (c : Name) (ls : List Level) (T : Type)
  | app1 (c : Name) (ls : List Level) (G : Type → Type) (f : Form)
  | arrow (a b : Form)

def Form.vars : Form → List Nat
  | .var p => [p]
  | .cst .. => []
  | .app1 _ _ _ f => f.vars
  | .arrow a b => a.vars ++ b.vars

/-- The Lean type of a form, given the Lean types `ts` of the earlier (type) arguments. -/
def Form.ty : Form → List Type → Type
  | .var p, ts => ts.getD p PUnit
  | .cst _ _ T, _ => T
  | .app1 _ _ G f, ts => G (f.ty ts)
  | .arrow a b, ts => a.ty ts → b.ty ts

inductive Binder : Type 1
  | ty
  | tm (F : Form)

def Binder.kind : Binder → Bool
  | .ty => false
  | .tm _ => true

/-- The binder name of an arrow in a declared type (`a._@._internal._hyg.0`). -/
def argName : Name := .num (.str (.str (.str (.str .anonymous "a") "_@") "_internal") "_hyg") 0

/-- The expression of the form `F` at binder position `j`, after the first `i` binders were replaced by `es`: a replaced argument is lifted over the `j - i` binders in between; a not-yet-replaced one is its bound variable. -/
def FE (es : List Expr) (i : Nat) : Nat → Form → Expr
  | j, .var p => if p < i then liftS (es.getD p (.bvar 0)) 0 (j - i) else .bvar (j - 1 - p)
  | _, .cst c ls _ => .const c ls
  | j, .app1 c ls _ f => .app (.const c ls) (FE es i j f)
  | j, .arrow a b => .forallE argName (FE es i j a) (FE es i (j + 1) b) .default

/-- The telescope `T` whose leading binder is binder `j`, when the first `i` binders have been replaced by `es`: the binders are `bs` (a type binder is a `Sort`, a term binder has the type of its form). -/
def Post (es : List Expr) (i : Nat) : Nat → Expr → List Binder → Prop
  | _, _, [] => True
  | j, T, .ty :: bs => ∃ (x : Name) (u : Level) (B : Expr) (bi : BinderInfo), T = .forallE x (.sort u) B bi ∧ Post es i (j + 1) B bs
  | j, T, .tm F :: bs => ∃ (x : Name) (B : Expr) (bi : BinderInfo), T = .forallE x (FE es i j F) B bi ∧ Post es i (j + 1) B bs

/-- Every variable of a form at position `j` is an earlier binder. -/
def BoundB : Nat → List Binder → Prop
  | _, [] => True
  | j, .ty :: bs => BoundB (j + 1) bs
  | j, .tm F :: bs => (∀ p ∈ F.vars, p < j) ∧ BoundB (j + 1) bs

/-- The variables of a form refer to TYPE binders among the first `pre.length` (`pre` records which are type binders). -/
def wfB : List Binder → List Bool → Bool
  | [], _ => true
  | .ty :: bs, pre => wfB bs (pre ++ [true])
  | .tm F :: bs, pre => F.vars.all (fun p => pre.getD p false) && wfB bs (pre ++ [false])

theorem lt_of_getD_true : ∀ (pre : List Bool) (p : Nat), pre.getD p false = true → p < pre.length
  | [], p, h => by simp at h
  | b :: pre, 0, _ => by simp
  | b :: pre, p + 1, h => by
    have := lt_of_getD_true pre p (by simpa using h)
    simp; omega

theorem boundB_of_wfB : ∀ (rest : List Binder) (pre : List Bool), wfB rest pre = true → BoundB pre.length rest
  | [], _, _ => trivial
  | .ty :: bs, pre, h => by
    have := boundB_of_wfB bs (pre ++ [true]) h
    simpa [BoundB] using this
  | .tm F :: bs, pre, h => by
    simp only [wfB, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun p hp => lt_of_getD_true pre p (by simpa using h.1 p hp), ?_⟩
    have := boundB_of_wfB bs (pre ++ [false]) h.2
    simpa using this

theorem FE_subst (es : List Expr) (i : Nat) (a : Expr) (hl : es.length = i) :
    ∀ (F : Form) (j : Nat), i + 1 ≤ j → (∀ p ∈ F.vars, p < j) → substS (FE es i j F) (j - i - 1) a = FE (es ++ [a]) (i + 1) j F
  | .var p, j, hj, hp => by
    have hpj : p < j := hp p (by simp [Form.vars])
    simp only [FE]
    by_cases h1 : p < i
    · have h2 : p < i + 1 := by omega
      simp only [h1, h2, if_true]
      rw [substS_liftS_in _ 0 (j - i) (j - i - 1) a (Nat.zero_le _) (by omega)]
      have : (es ++ [a]).getD p (.bvar 0) = es.getD p (.bvar 0) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show p < es.length by omega)]
      rw [this]
      congr 1
    · by_cases h3 : p = i
      · subst h3
        have h2 : p < p + 1 := by omega
        simp only [h1, h2, if_false, if_true]
        have : (es ++ [a]).getD p (.bvar 0) = a := by
          simp [List.getD_eq_getElem?_getD, hl]
        rw [this]
        have e1 : j - 1 - p = j - p - 1 := by omega
        rw [e1]
        simp [substS]
        congr 1
      · have h2 : ¬ p < i + 1 := by omega
        simp only [h1, h2, if_false]
        have e1 : j - 1 - p < j - i - 1 := by omega
        simp [substS, e1]
  | .cst c ls T, j, _, _ => by simp [FE, substS]
  | .app1 c ls G f, j, hj, hp => by
    simp only [FE, substS]
    rw [FE_subst es i a hl f j hj (fun p hq => hp p (by simpa [Form.vars] using hq))]
  | .arrow x y, j, hj, hp => by
    simp only [FE, substS]
    have hx := FE_subst es i a hl x j hj (fun p hq => hp p (by simp [Form.vars, hq]))
    have hy := FE_subst es i a hl y (j + 1) (by omega) (fun p hq => by have := hp p (by simp [Form.vars, hq]); omega)
    rw [show j - i - 1 + 1 = j + 1 - i - 1 by omega, hx, hy]

end Tools.ShippingGen5PTCorpusTele
