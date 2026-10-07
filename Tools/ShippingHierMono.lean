import Tools.ShippingHierStateG

/-! # The stateful run, monotone in the design

A run that succeeds with children map `G₁` succeeds, with the same result,
with any map `G₂` extending it (`G₁ x = some r → G₂ x = some r`): every
lookup the run makes succeeded under `G₁`. A child module compiled in its own
design therefore runs the same inside its parent's design, when the parent's
design finds every module of the child's design by its name. -/
namespace Tools.ShippingHierMono
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierarchySoundness Tools.ShippingHierState Tools.ShippingHierStateG

/-- `G₂` extends `G₁`. -/
def Extends (G₁ G₂ : String → Option (Module × WEnv)) : Prop :=
  ∀ x r, G₁ x = some r → G₂ x = some r

/-- `KS₂` extends `KS₁` on every successful step. -/
def StepExtends {σ : Type} (KS₁ KS₂ : KStep σ) : Prop :=
  ∀ child cwe cin env s r, KS₁ child cwe cin env s = some r → KS₂ child cwe cin env s = some r

theorem evalAssignsKG_mono {σ : Type} {KS₁ KS₂ : KStep σ} (hKS : StepExtends KS₁ KS₂)
    {G₁ G₂ : String → Option (Module × WEnv)} (hG : Extends G₁ G₂) (we : WEnv)
    (kids : String → σ) (mems : MEnv) :
    ∀ (body : List Stmt) (env : Env) (acc : String → σ) r,
      evalAssignsKG KS₁ we G₁ kids mems body env acc = some r →
      evalAssignsKG KS₂ we G₂ kids mems body env acc = some r
  | [], _, _, _, h => h
  | .assign l e :: rest, env, acc, r, h => by
    simp only [evalAssignsKG] at h ⊢
    cases hv : evalExpr we env e with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_eq_bind, Option.bind_some] at h ⊢
      exact evalAssignsKG_mono hKS hG we kids mems rest _ acc r h
  | .inst mn iname conns :: rest, env, acc, r, h => by
    simp only [evalAssignsKG] at h ⊢
    cases hc : G₁ mn with
    | none => rw [hc] at h; cases h
    | some cp =>
      rw [hc] at h
      rw [hG mn cp hc]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases hk : KS₁ cp.1 cp.2 (inConns cp.1.outputs conns) env (kids iname) with
      | none => rw [hk] at h; cases h
      | some kr =>
        rw [hk] at h
        rw [hKS _ _ _ _ _ kr hk]
        simp only [Option.bind_some] at h ⊢
        exact evalAssignsKG_mono hKS hG we kids mems rest _ _ r h
  | .register .. :: rest, env, acc, r, h => by
    simp only [evalAssignsKG] at h ⊢
    exact evalAssignsKG_mono hKS hG we kids mems rest env acc r h
  | .memory nm aw dw c wa wd wen ra rd cr ew er :: rest, env, acc, r, h => by
    simp only [evalAssignsKG] at h ⊢
    split at h
    · rename_i hcr
      rw [if_pos hcr]
      cases hcm : comboReads we mems nm aw dw ((ra, rd) :: er) env with
      | none => simp [hcm] at h
      | some env' =>
        simp only [hcm, Option.bind_eq_bind, Option.bind_some] at h ⊢
        exact evalAssignsKG_mono hKS hG we kids mems rest _ acc r h
    · rename_i hcr
      rw [if_neg hcr]
      exact evalAssignsKG_mono hKS hG we kids mems rest env acc r h

theorem stepModuleTG_mono {σ : Type} {KS₁ KS₂ : KStep σ} (hKS : StepExtends KS₁ KS₂)
    {G₁ G₂ : String → Option (Module × WEnv)} (hG : Extends G₁ G₂) (we : WEnv)
    (body : List Stmt) (env0 : Env) (s : KState σ) (r : Env × KState σ)
    (h : stepModuleTG KS₁ we G₁ body env0 s = some r) :
    stepModuleTG KS₂ we G₂ body env0 s = some r := by
  unfold stepModuleTG at h ⊢
  cases hE : evalAssignsKG KS₁ we G₁ s.kids s.mems body env0 s.kids with
  | none => rw [hE] at h; cases h
  | some ek =>
    rw [hE] at h
    rw [evalAssignsKG_mono hKS hG we s.kids s.mems body env0 s.kids ek hE]
    exact h

theorem runModuleTG_mono {σ : Type} {KS₁ KS₂ : KStep σ} (hKS : StepExtends KS₁ KS₂)
    {G₁ G₂ : String → Option (Module × WEnv)} (hG : Extends G₁ G₂) (we : WEnv)
    (body : List Stmt) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (s : KState σ) envs, runModuleTG KS₁ we G₁ body seed k s = some envs →
      runModuleTG KS₂ we G₂ body seed k s = some envs
  | 0, _, _, h => h
  | k + 1, s, envs, h => by
    simp only [runModuleTG] at h ⊢
    cases hS : stepModuleTG KS₁ we G₁ body (seed k s.st) s with
    | none => rw [hS] at h; cases h
    | some r =>
      rw [hS] at h
      rw [stepModuleTG_mono hKS hG we body _ s r hS]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases hR : runModuleTG KS₁ we G₁ body seed k r.2 with
      | none => rw [hR] at h; cases h
      | some rest =>
        rw [hR] at h
        rw [runModuleTG_mono hKS hG we body seed k r.2 rest hR]
        exact h

/-- **The depth-`n` step is monotone in the design.** -/
theorem KSn_mono {G₁ G₂ : String → Option (Module × WEnv)} (hG : Extends G₁ G₂) :
    ∀ n, StepExtends (KSn G₁ n) (KSn G₂ n)
  | 0 => fun _ _ _ _ _ _ h => h
  | n + 1 => by
    intro child cwe cin env s r h
    exact stepModuleTG_mono (KSn_mono hG n) hG cwe child.body _ s r h

end Tools.ShippingHierMono
