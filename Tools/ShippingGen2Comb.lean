import Tools.ShippingMachineDepthHR
import Tools.ShippingMachineShipsComb
set_option autoImplicit false

/-! # M2-step S1: reset irrelevance of an assignment-only body (scripts/gen2/STEP_IFACE_FREEZE.md §4 S1)

Pure. An assignment-only body closed over its reads `X` runs the same, cycle by cycle on `X` and on the names it
writes, under two seeds that agree on `X`. With `"rst" ∉ X` this moves a run whose seed holds reset low to the
canonical `seedIn` seeding, whatever the state holds at `"rst"`. Independent of the `ChildShips` edit. -/
namespace Tools.ShippingGen2Comb
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (isAssign)
open Tools.ShippingMachineShipsComb (regNexts_assigns memNexts_assigns applyNexts_nil)

/-- An assignment-only body has no memory statement. -/
theorem memFree_of_assigns : ∀ {body : List Stmt}, body.all isAssign = true → Tools.ConeFold.memFree body
  | [], _ => trivial
  | st :: rest, h => by
    have h2 : rest.all isAssign = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    have ih := memFree_of_assigns (body := rest) h2
    cases st with
    | assign l e => exact ih
    | _ => simp [isAssign] at h

/-- **S1** (frozen type, §4 S1). -/
theorem runModule_seed_local {we : WEnv} {body : List Stmt} {X : List String}
    (hA : body.all isAssign = true) (hR : readsClosedB X body = true)
    {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st, ∀ x ∈ X, seed₁ t st x = seed₂ t st x) :
    ∀ T st mems envs₁, runModule we body seed₁ T st mems = some envs₁ →
      ∃ envs₂, runModule we body seed₂ T st mems = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) x, x ∈ X ++ writesOf body →
          (envs₂[j]'h₂) x = (envs₁[j]'h₁) x
  | 0, _, _, envs, h => by
    simp only [runModule, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, fun j hj => by simp at hj⟩
  | k + 1, st, mems, envs, h => by
    simp only [runModule, stepModule] at h ⊢
    cases he : evalAssigns we mems body (seed₁ k st) with
    | none => simp [he] at h
    | some e =>
      obtain ⟨e', he', hP⟩ := Tools.ShippingHierOptRunH.evalAssigns_local we mems body X
        (seed₁ k st) (seed₂ k st) e (memFree_of_assigns hA)
        (by rw [← Tools.ShippingMachineDepthHR.readsClosedB_eq]; exact hR)
        (fun n hn => hagree k st n hn) he
      simp only [he, he', regNexts_assigns hA, memNexts_assigns hA, Option.bind_eq_bind, Option.bind_some,
        applyNexts_nil] at h ⊢
      cases hr : runModule we body seed₁ k st mems with
      | none => simp [hr] at h
      | some rest =>
        simp only [hr, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨rest', hr', hl, hc⟩ := runModule_seed_local hA hR hagree k st mems rest hr
        refine ⟨e' :: rest', by simp [hr'], by simp [hl], ?_⟩
        intro j h₁ h₂ x hx
        cases j with
        | zero => exact hP x hx
        | succ j => exact hc j (by simpa using h₁) (by simpa using h₂) x hx

end Tools.ShippingGen2Comb
