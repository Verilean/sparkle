import Lean
import Sparkle.Compiler.ExprDecEq

/-! # A decidable check of an environment against finite tables of facts

`defsOkB env l` / `ctorsOkB env l` / `recOkB env` read the constants listed in `l` out of `env`
(`Environment.find?`) and compare the stored fields with the rows, with the Lean-written
decision procedure `ExprDecEq.exprDecEq` on `Expr` (core's `==` on `Expr` is opaque).
The soundness lemmas say what `true` means: for every row, `env.find? c` is the stated kind of
declaration and its level parameters / value (definition), inductive / numParams / numFields
(constructor) agree with the row; `recOkB env = true` means `List.rec` is a recursor.
Nothing here is trusted: no `sorry`, `axiom`, `native_decide`. -/
namespace Sparkle.Compiler.EnvTableCheck
open Lean

def exprEqB (a b : Expr) : Bool := @decide (a = b) (Sparkle.Compiler.ExprDecEq.exprDecEq a b)

theorem exprEqB_iff {a b : Expr} : exprEqB a b = true ↔ a = b := by
  unfold exprEqB; exact @decide_eq_true_iff _ (Sparkle.Compiler.ExprDecEq.exprDecEq a b)

/-- a definition row: name, universe parameters, value -/
def defRowOkB (env : Environment) (c : Name) (lps : List Name) (v : Expr) : Bool :=
  match env.find? c with
  | some (.defnInfo d) => decide (d.levelParams = lps) && exprEqB d.value v
  | _ => false

theorem defRowOkB_sound {env : Environment} {c : Name} {lps : List Name} {v : Expr} (h : defRowOkB env c lps v = true) :
    ∃ d : DefinitionVal, env.find? c = some (.defnInfo d) ∧ d.levelParams = lps ∧ d.value = v := by
  unfold defRowOkB at h
  split at h
  · rename_i d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨d, hd, h.1, exprEqB_iff.1 h.2⟩
  · cases h

/-- a constructor row: name, inductive, numParams, numFields -/
def ctorRowOkB (env : Environment) (c ind : Name) (np nf : Nat) : Bool :=
  match env.find? c with
  | some (.ctorInfo cv) => decide (cv.induct = ind) && decide (cv.numParams = np) && decide (cv.numFields = nf)
  | _ => false

theorem ctorRowOkB_sound {env : Environment} {c ind : Name} {np nf : Nat} (h : ctorRowOkB env c ind np nf = true) :
    ∃ cv : ConstructorVal, env.find? c = some (.ctorInfo cv) ∧ cv.induct = ind ∧ cv.numParams = np ∧ cv.numFields = nf := by
  unfold ctorRowOkB at h
  split at h
  · rename_i cv hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨cv, hc, h.1.1, h.1.2, h.2⟩
  · cases h

/-- `List.rec` is a recursor of the environment -/
def recOkB (env : Environment) : Bool :=
  match env.find? ``List.rec with
  | some (.recInfo _) => true
  | _ => false

theorem recOkB_sound {env : Environment} (h : recOkB env = true) :
    ∃ ri : RecursorVal, env.find? ``List.rec = some (.recInfo ri) := by
  unfold recOkB at h
  split at h
  · rename_i ri hr; exact ⟨ri, hr⟩
  · cases h

def defsOkB (env : Environment) (l : List (Name × List Name × Expr)) : Bool :=
  l.all fun p => defRowOkB env p.1 p.2.1 p.2.2

theorem defsOkB_sound {env : Environment} {l : List (Name × List Name × Expr)} (h : defsOkB env l = true) :
    ∀ p ∈ l, ∃ d : DefinitionVal, env.find? p.1 = some (.defnInfo d) ∧ d.levelParams = p.2.1 ∧ d.value = p.2.2 := by
  intro p hp
  exact defRowOkB_sound (List.all_eq_true.1 h p hp)

def ctorsOkB (env : Environment) (l : List (Name × Name × Nat × Nat)) : Bool :=
  l.all fun p => ctorRowOkB env p.1 p.2.1 p.2.2.1 p.2.2.2

theorem ctorsOkB_sound {env : Environment} {l : List (Name × Name × Nat × Nat)} (h : ctorsOkB env l = true) :
    ∀ p ∈ l, ∃ cv : ConstructorVal, env.find? p.1 = some (.ctorInfo cv) ∧ cv.induct = p.2.1 ∧ cv.numParams = p.2.2.1 ∧ cv.numFields = p.2.2.2 := by
  intro p hp
  exact ctorRowOkB_sound (List.all_eq_true.1 h p hp)

end Sparkle.Compiler.EnvTableCheck
