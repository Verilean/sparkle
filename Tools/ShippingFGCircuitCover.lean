import Tools.ShippingFGCircuitArtifact
set_option autoImplicit false
-- FG circuit pilot S1d, units 2 and 4: `hP` (`genGP` returns a package for a leaf root) and the `data` / `kD` part of `hl`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `genGP` covers a leaf root; the package's data is the reader's data

For a root `X` whose reader data `d` has no instances (all four roots: `insts = []`), `genS` needs no callee, so the coverage question (`ReachCover`) is the single-name
statement: the generated-data table `genData₀ env` has a row `g` for the entry constant of `X`. `genGP_some_of_leaf` proves `genGP … X = some p` from that row;
`genGP_root` adds `p.d = g.d` and `p.kD = kDOf g.d` (the `data` and `kD_eq` conjuncts of `EndpointLink`).

The row `g` is a `GenData`: it carries `GenWF`, `machineShape? … = some d.shape` and `dataOfAt lvl E senv d.shape = some d`. For the canonical table `canonGD` (choice of a `GenData` when one exists) the
row exists exactly when those three facts hold of some `d` for the entry constant of `X` (`RootReader`): that is the reader ↔ model agreement of the root (`dataOfAt` = `readMachine` at the
literal `X.machineData`). It is an environment-and-reader fact (FG rows: C.SM-1 `hs` is separate; DG-DATAOF / DG-COVER / DG-ENV), checkable in `MetaM` on the snapshot
(`FGCircuitPilotCheck3` runs it), not provable by the kernel because `dataOfAt` calls the `partial` helpers `packTupleInputs` / `rootFloat`. -/
namespace Tools.ShippingFGCircuitCover
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Tools.ShippingGen5Sem (kDOf GenWF)
open Tools.ShippingGen5SM1

theorem genSemI_kD {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) :
    (genSemI Q X g).kD = kDOf g.d := by
  unfold genSemI; split <;> rfl

section
variable {ι : Type} {dom : ι → DomainConfig}

/-- `genGP` returns a package for a leaf root whose table row exists; the package's data is the row's data and its `kD` is `kDOf`. -/
theorem genGP_root (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env)))
    (env : Environment) {X : Name} {E : ConstantInfo} {g : GenData (dataOfAt lvl) E (structEnv env)}
    (hE : entry₀ env X = some E) (hg : genData₀ env E = some g) (hleaf : g.d.shape.insts = []) :
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some p ∧ p.decl = X ∧ p.d = g.d ∧ p.kD = kDOf g.d := by
  let K := genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
  have hgK : K.genData₀ E = some g := hg
  have hd0 : dataOf₀ K X = some g.d := dataOf₀_of_genData₀ K hE hgK
  have hacc : Acc (CallRel K) X := by
    refine Acc.intro X fun y hy => ?_
    obtain ⟨d, hd, k, hk, -, -⟩ := hy
    rw [hd0] at hd
    have hd' : d = g.d := (Option.some.inj hd).symm
    subst hd'
    rw [hleaf] at hk
    exact absurd hk (by simp)
  have hunf := genS_unfold K hacc hE hgK
  have hall : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome := by
    intro k _
    have hlen : (K.dOf g).shape.insts.length = 0 := by
      show g.d.shape.insts.length = 0
      rw [hleaf]; rfl
    have := k.2
    omega
  rw [if_pos hall] at hunf
  have hF := factsOf_genS_assembled'' (ι := ι) (dom := dom) hs (genData₀ env)
  have hP := genP_eq_some K hF hunf
  have hpp : genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some _ := hP
  refine ⟨_, hpp, ?_, ?_, ?_⟩
  · exact genP_decl K hF hP
  · obtain ⟨d', hd', hpd⟩ := genP_d_edges K hF hP
    rw [hd0] at hd'
    rw [hpd, ← Option.some.inj hd']
  · obtain ⟨s, hs', hps⟩ := genP_some_inv K hF hP
    rw [hunf] at hs'
    have hs'' : s = K.genSem (genS K) X g := (Option.some.inj hs').symm
    rw [← kD_toSem, hps, hs'']
    exact genSemI_kD _ _ _


open Classical in
/-- the canonical generated-data table: a `GenData` row where one exists (choice), `none` elsewhere -/
noncomputable def canonGD (lvl : Lean.Expr → Nat) (env : Environment) (E : ConstantInfo) :
    Option (GenData (dataOfAt lvl) E (structEnv env)) :=
  if h : Nonempty (GenData (dataOfAt lvl) E (structEnv env)) then some (Classical.choice h) else none

/-- reader ↔ model agreement of a root (named; checked in `MetaM` on the snapshot, not provable by the kernel: `dataOfAt` calls the `partial` helpers) -/
def RootReader (lvl : Lean.Expr → Nat) (env : Environment) (X : Name) (d : MachineData) : Prop :=
  ∃ E : ConstantInfo, entry₀ env X = some E ∧ machineShape? false [] E (structEnv env) = some d.shape ∧
    dataOfAt lvl E (structEnv env) d.shape = some d

theorem canon_row {lvl : Lean.Expr → Nat} {env : Environment} {E : ConstantInfo} {d : MachineData} (hwf : GenWF d = true)
    (hsh : machineShape? false [] E (structEnv env) = some d.shape) (hdat : dataOfAt lvl E (structEnv env) d.shape = some d) :
    ∃ g : GenData (dataOfAt lvl) E (structEnv env), canonGD lvl env E = some g ∧ g.d = d := by
  have hne : Nonempty (GenData (dataOfAt lvl) E (structEnv env)) := ⟨⟨d, hwf, hsh, hdat⟩⟩
  refine ⟨Classical.choice hne, by unfold canonGD; exact dif_pos hne, ?_⟩
  have h2 : d.shape = (Classical.choice hne).d.shape := Option.some.inj (hsh.symm.trans (Classical.choice hne).hshape)
  have h3 := (Classical.choice hne).hdata
  rw [← h2, hdat] at h3
  exact (Option.some.inj h3).symm

/-- `hP` and the `data` / `kD` parts of `hl` for a leaf root, from `RootReader` (the canonical table has the row) -/
theorem genGP_root_canon {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name} {d : MachineData}
    (hR : RootReader lvl env X d) (hwf : GenWF d = true) (hleaf : d.shape.insts = []) :
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env X = some p ∧
      p.decl = X ∧ p.d = d ∧ p.kD = kDOf d := by
  obtain ⟨E, hE, hsh, hdat⟩ := hR
  obtain ⟨g, hg, hgd⟩ := canon_row (lvl := lvl) (env := env) hwf hsh hdat
  have hleaf' : g.d.shape.insts = [] := by rw [hgd]; exact hleaf
  obtain ⟨p, hp, hdecl, hpd, hkD⟩ := genGP_root (ι := ι) (dom := dom) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env hE hg hleaf'
  exact ⟨p, hp, hdecl, hpd.trans hgd, hkD.trans (by rw [hgd])⟩

end

end Tools.ShippingFGCircuitCover

#print axioms Tools.ShippingFGCircuitCover.genGP_root
#print axioms Tools.ShippingFGCircuitCover.genGP_root_canon
