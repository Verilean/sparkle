import Lean.Expr
import Lean.Syntax

/-! # Decidable equality on `Lean.Expr`, in Lean

Core compares expressions with `Expr.equal`, an opaque `@[extern]` function:
nothing can be proved about it (no `EquivBEq`/`LawfulBEq`, and `true` cannot be
shown to mean equal). This module gives a decision procedure written in Lean,
`exprDecEq : (a b : Expr) → Decidable (a = b)`, with standard axioms only.

`withPtrEqDecEq` puts a pointer-equality fast path at every node (logically the
structural decision). Without it, comparing two DAG-shaped expressions unfolds
them into trees: measured on the translator's cache validation, Keccak256Sponge
went from 3.3 s to 54 s; with the fast path it is within ~1.5 s of baseline.

`mdata` payloads reach `Syntax`, a nested inductive that `deriving` refuses, so
`synEq` / `synEq_iff` are written by hand. `Level` carries a `computed_field`,
so `levEq` / `levEq_iff` are too.

`exprDecEq` is a definition, not an instance, and the leaf instances are ones
core does not provide, so `==` elsewhere keeps resolving to core's instances. -/

namespace Sparkle.Compiler.ExprDecEq
open Lean
deriving instance DecidableEq for String.Pos.Raw
deriving instance DecidableEq for Substring.Raw
deriving instance DecidableEq for SourceInfo
deriving instance DecidableEq for Syntax.Preresolved
mutual
def synEq : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node i k a, .node i' k' a' => decide (i = i') && decide (k = k') && synArrEq a a'
  | .atom i v, .atom i' v' => decide (i = i') && decide (v = v')
  | .ident i r v p, .ident i' r' v' p' => decide (i = i') && decide (r = r') && decide (v = v') && decide (p = p')
  | _, _ => false
def synArrEq : Array Syntax → Array Syntax → Bool
  | ⟨l⟩, ⟨l'⟩ => synListEq l l'
def synListEq : List Syntax → List Syntax → Bool
  | [], [] => true
  | x :: xs, y :: ys => synEq x y && synListEq xs ys
  | _, _ => false
end

mutual
theorem synEq_iff : ∀ a b : Syntax, synEq a b = true ↔ a = b
  | .missing, b => by cases b <;> simp [synEq]
  | .node i k a, b => by
    cases b with
    | node i' k' a' => simp [synEq, synArrEq_iff a a', and_assoc]
    | _ => simp [synEq]
  | .atom i v, b => by cases b <;> simp [synEq]
  | .ident i r v p, b => by cases b <;> simp [synEq, and_assoc]
theorem synArrEq_iff : ∀ a b : Array Syntax, synArrEq a b = true ↔ a = b
  | ⟨l⟩, ⟨l'⟩ => by simp [synArrEq, synListEq_iff l l']
theorem synListEq_iff : ∀ a b : List Syntax, synListEq a b = true ↔ a = b
  | [], b => by cases b <;> simp [synListEq]
  | x :: xs, b => by
    cases b with
    | nil => simp [synListEq]
    | cons y ys => simp [synListEq, synEq_iff x y, synListEq_iff xs ys]
end

instance synDecEq : DecidableEq Syntax := fun a b => decidable_of_iff _ (synEq_iff a b)
deriving instance DecidableEq for DataValue
deriving instance DecidableEq for KVMap
deriving instance DecidableEq for Literal
deriving instance DecidableEq for BinderInfo

def levEq : Level → Level → Bool
  | .zero, .zero => true
  | .succ a, .succ b => levEq a b
  | .max a b, .max c d => levEq a c && levEq b d
  | .imax a b, .imax c d => levEq a c && levEq b d
  | .param a, .param b => decide (a = b)
  | .mvar a, .mvar b => decide (a.name = b.name)
  | _, _ => false
theorem levEq_iff : ∀ a b : Level, levEq a b = true ↔ a = b := by
  intro a
  induction a with
  | zero => intro b; cases b <;> simp [levEq]
  | succ x ih => intro b; cases b <;> simp [levEq, ih]
  | max x y ihx ihy => intro b; cases b <;> simp [levEq, ihx, ihy]
  | imax x y ihx ihy => intro b; cases b <;> simp [levEq, ihx, ihy]
  | param n => intro b; cases b <;> simp [levEq]
  | mvar m =>
      intro b
      cases b <;> try simp [levEq]
      rename_i m2
      cases m; cases m2
      simp [levEq, Lean.LevelMVarId.mk.injEq]
instance levDecEq : DecidableEq Level := fun a b => decidable_of_iff _ (levEq_iff a b)
example : DecidableEq (List Level) := inferInstance
deriving instance DecidableEq for FVarId
deriving instance DecidableEq for MVarId
example : DecidableEq MData := inferInstance

/-- Decidable equality on `Lean.Expr`, written in Lean, with a pointer-equality
    fast path at EVERY node (`withPtrEqDecEq`: logically the structural
    decision, operationally a pointer check first). Shared subterms therefore
    cost O(1), so comparing two DAGs does not unfold them into trees. -/
def exprDecEq (a b : Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    match a, b with
    | .bvar i, .bvar j => if h : i = j then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .bvar _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .bvar _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar x, .fvar y => if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .fvar _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .fvar _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar x, .mvar y => if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .mvar _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mvar _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .sort u, .sort v => if h : u = v then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .sort _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .sort _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .const n us, .const m vs =>
      if h : n = m ∧ us = vs then isTrue (by rw [h.1, h.2]) else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
    | .const _ _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .const _ _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .app f x, .app g y =>
      match exprDecEq f g, exprDecEq x y with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .app _ _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .app _ _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lam n t b bi, .lam n' t' b' bi' =>
      match exprDecEq t t', exprDecEq b b' with
      | isTrue h1, isTrue h2 =>
        if h : n = n' ∧ bi = bi' then isTrue (by rw [h.1, h.2, h1, h2])
        else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .lam _ _ _ _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lam _ _ _ _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE n t b bi, .forallE n' t' b' bi' =>
      match exprDecEq t t', exprDecEq b b' with
      | isTrue h1, isTrue h2 =>
        if h : n = n' ∧ bi = bi' then isTrue (by rw [h.1, h.2, h1, h2])
        else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .forallE _ _ _ _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .forallE _ _ _ _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .letE n t v b nd, .letE n' t' v' b' nd' =>
      match exprDecEq t t', exprDecEq v v', exprDecEq b b' with
      | isTrue h1, isTrue h2, isTrue h3 =>
        if h : n = n' ∧ nd = nd' then isTrue (by rw [h.1, h.2, h1, h2, h3])
        else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
      | isFalse h, _, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .letE _ _ _ _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .letE _ _ _ _ _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit l, .lit l' => if h : l = l' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .lit _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .lit _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .mdata d x, .mdata d' x' =>
      match exprDecEq x x' with
      | isTrue h1 =>
        if h : d = d' then isTrue (by rw [h, h1]) else isFalse (by intro e; cases e; exact h rfl)
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .mdata _ _, .proj _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .bvar _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .fvar _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .mvar _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .sort _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .const _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .app _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .lam _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .forallE _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .letE _ _ _ _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .lit _ => isFalse (fun e => Expr.noConfusion e)
    | .proj _ _ _, .mdata _ _ => isFalse (fun e => Expr.noConfusion e)
    | .proj s i x, .proj s' i' x' =>
      match exprDecEq x x' with
      | isTrue h1 =>
        if h : s = s' ∧ i = i' then isTrue (by rw [h.1, h.2, h1]) else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)

end Sparkle.Compiler.ExprDecEq
