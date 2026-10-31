import Tools.ShippingGen5SemAccStep
set_option autoImplicit false
-- NOT BUILT HERE (U7, scripts/gen5/DG_SEM_FREEZE_P7.md; built clean as smu17v-9150ffd7, exit 0, approved at 9150ffd7; header/comment sync only). No sorry/axiom/native_decide.
/-! # DG-SEM U7 (scripts/gen5/DG_SEM_FREEZE_P7.md §3.1): `hunf_of_kitInv`, `factsOf_all_of_kitInv`

Kit-shaped premises (`hsem`, `hd`, `hmem`, `hinv`) are explicit variables, not laws. Nothing here supplies them for the real
`genS`, `GenData.toIn`, a run, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}

theorem ordCallees_transport (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (d d' : MachineData) (h : d = d') (k : Fin d.shape.insts.length) (hk : k ∈ ordCallees d) :
    ∃ k' : Fin d'.shape.insts.length, k' ∈ ordC d' ∧ (d.shape.insts[k]).1 = (d'.shape.insts[k']).1 := by
  subst h
  exact ⟨k, (hmem d k).2 ((mem_ordCallees d k).1 hk), rfl⟩

theorem hunf_of_kitInv
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd) :
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y := by
  intro Y s _ hs
  obtain ⟨E, gd, _, hedge, hseq⟩ := hinv Y s hs
  refine ⟨toIn gd, hseq.trans (hsem G Y gd), ?_⟩
  intro k hk
  obtain ⟨k', hk', he⟩ := ordCallees_transport ordC hmem _ _ (hd gd) k hk
  rw [he]
  exact hedge k' hk'

theorem factsOf_all_of_kitInv
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s :=
  factsOf_all_of_acc_unfold R G (hunf_of_kitInv GD toIn dOf ordC genSemK R G hsem hd hmem hinv)
    (fun Y s hs => (hinv Y s hs).choose_spec.choose_spec.1)

end Tools.ShippingGen5Sem
