import Tools.ShippingGen5ConstValueE
set_option autoImplicit false
/-! # `LS env X`: a deterministic level choice for `ConstValueE` (DCF-4 design, reviewer decision; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §LS)

`ls` is not fixed to `[]`: each `(env, X)` gets a deterministic level list `LS env X`, one level per `levelParams` of `env.find? X`
(`Level.zero` each). `CVLS PT := fun env X α v => ConstValueEAt PT env X (LS env X) α v` has the type `ConstValueRel`, so universe-polymorphic
constants are not excluded up front. No axiom, no `sorry`, no TRUSTED; `PT` stays arbitrary. The soundness obligations
(`OblLevelErase`, `OblLiftClosed`, ...) are neither assumed nor proved. -/
namespace Tools.ShippingGen5ConstValueE
open Lean

/-- The levels chosen for `X` in `env`: `Level.zero` for each level parameter of its declaration (`[]` if `X` is absent). -/
def LS (env : Environment) (X : Name) : List Level :=
  match env.find? X with
  | some ci => ci.levelParams.map (fun _ => Level.zero)
  | none => []

theorem LS_length (env : Environment) (X : Name) (ci : ConstantInfo) (h : env.find? X = some ci) :
    (LS env X).length = ci.levelParams.length := by
  simp [LS, h]

theorem LS_none (env : Environment) (X : Name) (h : env.find? X = none) : LS env X = [] := by
  simp [LS, h]

/-- `ConstValueE` with the level list chosen by `LS` (no `∃ ls`). -/
def CVLS (PT : PrimTable) (env : Environment) (X : Name) (α : Type) (v : α) : Prop :=
  ConstValueEAt PT env X (LS env X) α v

theorem cvls_functional (PT : PrimTable) (env : Environment) (X : Name) {α β : Type} {v : α} {w : β}
    (h : CVLS PT env X α v) (h' : CVLS PT env X β w) : α = β ∧ HEq v w :=
  constValueEAt_functional PT env X (LS env X) h h'

end Tools.ShippingGen5ConstValueE
