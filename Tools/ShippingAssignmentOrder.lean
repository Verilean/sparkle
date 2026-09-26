import Sparkle.IR.ReorderInvariance
import Sparkle.IR.OptCheck

/-! # Ordered IR assignments and simultaneous equations

Independent of compiler entry and SV printing proofs.
-/
namespace Tools.ShippingSettledSoundness
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder

/-- Each target is written once, and an RHS reads neither its own target
nor a target that will be assigned later. Names not written by the body are
external inputs. No expression shape or fixed circuit size is assumed. -/
inductive Acyclic : List Stmt → Prop
  | nil : Acyclic []
  | cons {l r rest}
      (target : l ∉ writesOf rest)
      (reads : ∀ x ∈ refsOf r, x ≠ l ∧ x ∉ writesOf rest)
      (tail : Acyclic rest) : Acyclic (.assign l r :: rest)

theorem writes_cons (l : String) (r : Sparkle.IR.AST.Expr) (rest : List Stmt) :
    writesOf (.assign l r :: rest) = l :: writesOf rest := rfl

/-- All equations are evaluated in the SAME environment. -/
def IREquations (we : WEnv) (body : List Stmt) (env : Env) : Prop :=
  ∀ l r, Stmt.assign l r ∈ body → evalExpr we env r = some (env l)

/-- Undriven names retain their supplied values. -/
def ExternalValues (body : List Stmt) (initial env : Env) : Prop :=
  ∀ x, x ∉ writesOf body → env x = initial x

theorem assign_frame {we mems body initial env} (ha : Acyclic body)
    (he : evalAssigns we mems body initial = some env) :
    ExternalValues body initial env := by
  induction ha generalizing initial with
  | nil => simp [evalAssigns] at he; subst env; exact fun _ _ => rfl
  | @cons l r rest ht hr ha ih =>
    simp only [evalAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨v, _, he⟩ := he
    intro x hx
    have hx' : x ≠ l ∧ x ∉ writesOf rest := by
      simpa [writes_cons] using hx
    simpa [hx'.1] using ih he x hx'.2

/-- A successful ordered fold produces a simultaneous solution. -/
theorem assign_equations {we mems body initial env} (ha : Acyclic body)
    (he : evalAssigns we mems body initial = some env) : IREquations we body env := by
  induction ha generalizing initial with
  | nil => simp [IREquations]
  | @cons l r rest ht hr ha ih =>
    simp only [evalAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨v, hv, he⟩ := he
    have hf := assign_frame ha he
    have hl : env l = v := by simpa using hf l ht
    have hrhs : evalExpr we env r = evalExpr we initial r :=
      evalExpr_congr _ _ _ _ (fun x hx => by simpa [(hr x hx).1] using hf x (hr x hx).2)
    intro l' r' hm
    rcases List.mem_cons.mp hm with heq | hm
    · cases heq; exact hrhs.trans (hv.trans (congrArg some hl.symm))
    · exact ih he l' r' hm

/-- A simultaneous solution with the supplied external values is uniquely
recovered by the ordered fold. This also proves uniqueness of internal wires,
not only equality of the observed output. -/
theorem equations_eval {we mems body initial env} (ha : Acyclic body)
    (hq : IREquations we body env) (hx : ExternalValues body initial env) :
    evalAssigns we mems body initial = some env := by
  induction ha generalizing initial with
  | nil =>
    have he : initial = env := funext (fun x => (hx x (by simp [writesOf])).symm)
    simp [evalAssigns, he]
  | @cons l r rest ht hr ha ih =>
    have hv : evalExpr we initial r = some (env l) := by
      rw [evalExpr_congr we initial env r (fun x hm => (hx x (by
        have := hr x hm; simpa [writes_cons] using this)).symm)]
      exact hq l r (by simp)
    simp only [evalAssigns, hv]
    apply ih (fun l r hm => hq l r (by simp [hm]))
    intro x hxr
    by_cases hxl : x = l
    · simp [hxl]
    · simpa [hxl] using hx x (by simp [writes_cons, hxl, hxr])

theorem equations_unique {we body initial env₁ env₂} (ha : Acyclic body)
    (h₁ : IREquations we body env₁) (hx₁ : ExternalValues body initial env₁)
    (h₂ : IREquations we body env₂) (hx₂ : ExternalValues body initial env₂) : env₁ = env₂ := by
  have a := equations_eval (mems := fun _ _ => 0) ha h₁ hx₁
  have b := equations_eval (mems := fun _ _ => 0) ha h₂ hx₂
  exact Option.some.inj (a.symm.trans b)

/-- The equation relation is insensitive to textual order. A permutation
need not itself be a valid topological evaluation schedule. -/
theorem equations_perm {we body body' env} (hp : body.Perm body') :
    IREquations we body env ↔ IREquations we body' env := by
  constructor
  · exact fun h l r hm => h l r (hp.mem_iff.mpr hm)
  · exact fun h l r hm => h l r (hp.mem_iff.mp hm)

/-- The shipping acceptance check exactly characterizes ordered assignments. -/
theorem assignmentOrderCheck_iff (body : List Stmt) :
    Sparkle.IR.OptCheck.assignmentOrderCheck body = true ↔ Acyclic body := by
  induction body with
  | nil => simp [Sparkle.IR.OptCheck.assignmentOrderCheck]; exact .nil
  | cons st rest ih =>
    cases st with
    | assign l r =>
      simp only [Sparkle.IR.OptCheck.assignmentOrderCheck, Bool.and_eq_true,
        Bool.not_eq_true', List.all_eq_true, bne_iff_ne, ih]
      simp only [List.contains_eq_mem, decide_eq_false_iff_not]
      constructor
      · rintro ⟨⟨ht, hr⟩, ha⟩; exact .cons ht hr ha
      · intro ha; cases ha with | cons ht hr ha => exact ⟨⟨ht, hr⟩, ha⟩
    | _ => constructor <;> intro h <;> cases h

theorem checkedOptimize_order {m : Sparkle.IR.AST.Module}
    (hg : Sparkle.IR.OptCheck.simpleBody m = true) (ha : Acyclic m.body) :
    Acyclic (Sparkle.IR.OptCheck.checkedOptimize m).body := by
  unfold Sparkle.IR.OptCheck.checkedOptimize
  simp only [hg, if_true]
  split
  · rename_i hc
    exact (assignmentOrderCheck_iff _).mp (Bool.and_eq_true_iff.mp hc).2
  · exact ha

end Tools.ShippingSettledSoundness
