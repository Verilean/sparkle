import Tools.ShippingGen5Acc
import Tools.ShippingGen2Defs
set_option autoImplicit false
-- Clean issue-linked build ac6v-a88c3e9c (incremental kjob lake build): exit 0, 724 jobs, source=base=end, dirty=false, approved at a88c3e9c (earlier clean build ac5v-802381fe, approved at 802381fe) (earlier clean build ac4v-5aab73de, 714 jobs). Earlier Pod builds: g5ac-r3 at 174b92b3. No sorry / axiom / native_decide.

/-! # DG-ACC unit A3: the package table `genP` built from `genS` (scripts/gen5/DG_ACC_FREEZE_REV1.md §B.2, REV2 §B)

CONDITIONAL on the named premise `GenSFacts K` (every `genS`-package carries its arm's fact; owner DG-FACTS/DG-CAUSAL; not
supplied here) and, for `genP_pkg`, on `hacc`/`hcl`/`ReachCover`/`hOk`. Nothing here claims `GenSFacts`, `ReachCover` or
`hacc`. The kit fields `genSem_decl`/`genSem_d` are DG-SEM's (unbuilt); the statements below use them as kit fields. -/
namespace Tools.ShippingGen5Acc
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

section GenP
open Classical

variable (K : AssignKit ι dom env₀)

/-- Every package `genS` produces carries its arm's fact. NAMED PREMISE (not supplied). -/
def GenSFacts : Prop := ∀ X s, genS K X = some s → FactsOf s

/-- The package table: `genS`'s data with the fact re-attached. -/
noncomputable def genP (hF : GenSFacts K) (X : Name) : Option (Pkg ι dom) :=
  match h : genS K X with
  | some s => some (genPkg s (hF X s h))
  | none => none

def SemOfGenPStmt : Prop := ∀ (hF : GenSFacts K), semOf (genP K hF) = genS K

def GeneratedAtK (P : Pkgs ι dom) (X : Name) (E : ConstantInfo) (p : Pkg ι dom) : Prop :=
  ∃ g : K.GD E, p.toSem = K.genSem (semOf P) X g

def GenPGeneratedStmt : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p →
    ∃ E, entry₀ env₀ X = some E ∧ GeneratedAtK K (genP K hF) X E p

def GenPDeclStmt : Prop := ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → p.decl = X

def GenPDEdgesStmt : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → ∃ d, dataOf₀ K X = some d ∧ p.d = d

def GenPPkgStmt : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) (hacc : ∀ c, Reach c → Acc (CallRel K) c)
    (hcov : ReachCover K Reach) (hOk : ∀ c, Reach c → ∀ q, genP K hF c = some q → DataOk q),
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q

def GenPClosedStmt : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c),
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1

theorem genP_eq_some (hF : GenSFacts K) {X : Name} {s : SemPkg ι dom} (h : genS K X = some s) :
    genP K hF X = some (genPkg s (hF X s h)) := by
  unfold genP
  split
  · rename_i s' h'
    have e : s' = s := Option.some.inj (h'.symm.trans h)
    subst e
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem genP_eq_none (hF : GenSFacts K) {X : Name} (h : genS K X = none) : genP K hF X = none := by
  unfold genP
  split
  · rename_i s' h'
    rw [h] at h'
    cases h'
  · rfl

theorem genP_some_inv (hF : GenSFacts K) {X : Name} {p : Pkg ι dom} (h : genP K hF X = some p) :
    ∃ s, genS K X = some s ∧ p.toSem = s := by
  cases hs : genS K X with
  | none => rw [genP_eq_none K hF hs] at h; cases h
  | some s =>
    rw [genP_eq_some K hF hs] at h
    have e : genPkg s (hF X s hs) = p := Option.some.inj h
    subst e
    exact ⟨s, rfl, toSem_genPkg s _⟩

theorem semOf_genP : SemOfGenPStmt K := by
  intro hF
  funext X
  cases hs : genS K X with
  | none => unfold semOf; rw [genP_eq_none K hF hs]; rfl
  | some s =>
    unfold semOf
    rw [genP_eq_some K hF hs]
    simp [toSem_genPkg]

theorem genP_generated : GenPGeneratedStmt K := by
  intro hF X p h
  obtain ⟨s, hs, hps⟩ := genP_some_inv K hF h
  obtain ⟨E, g, hE, -, -, -, hsem⟩ := genS_some_inv K hs
  refine ⟨E, hE, g, ?_⟩
  rw [hps, hsem, semOf_genP K hF]

theorem genP_decl : GenPDeclStmt K := by
  intro hF X p h
  obtain ⟨s, hs, hps⟩ := genP_some_inv K hF h
  obtain ⟨E, g, -, -, -, -, hsem⟩ := genS_some_inv K hs
  rw [← decl_toSem, hps, hsem]
  exact K.genSem_decl _ _ _

theorem genP_d_edges : GenPDEdgesStmt K := by
  intro hF X p h
  obtain ⟨s, hs, hps⟩ := genP_some_inv K hF h
  obtain ⟨E, g, hE, hg, -, -, hsem⟩ := genS_some_inv K hs
  refine ⟨K.dOf g, dataOf₀_of_genData₀ K hE hg, ?_⟩
  rw [← d_toSem, hps, hsem]
  exact K.genSem_d _ _ _

theorem genP_pkg : GenPPkgStmt K := by
  intro hF Reach DataOk hcl hacc hcov hOk c hc
  obtain ⟨s, hs⟩ := genS_isSome_of_cover K hcl hacc hcov c hc
  have hp := genP_eq_some K hF hs
  refine ⟨_, hp, ?_, hOk c hc _ hp⟩
  exact genP_decl K hF hp

theorem genP_closed : GenPClosedStmt K := by
  intro hF Reach hcl c hc q hq k hk hch
  obtain ⟨d, hd, hqd⟩ := genP_d_edges K hF hq
  subst hqd
  exact hcl c _ hc ⟨q.d, hd, k, hk, hch, rfl⟩

end GenP

end Tools.ShippingGen5Acc
