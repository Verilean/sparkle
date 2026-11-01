import Tools.ShippingGen5AccGenDataKit
set_option autoImplicit false
-- NOT BUILT (draft; freeze scripts/gen5/GDCOVER01_FREEZE.md). No sorry / axiom / native_decide.

/-! # G0: `genDataC`, `genDataC_isSome_iff`, `reachCover_iff_sdw`, `peel_of_machineShape` (scripts/gen5/GDCOVER01_FREEZE.md)

`genDataC` is the `GenData`-typed classical choice (the `GenData` analogue of `genDataF`). `reachCover_iff_sdw` splits `ReachCover` of the kit
whose `genData₀` is `genDataC` into (S) shape / (D) data / (W) `GenWF`. No new premise; nothing here supplies (S), (D) or (W). -/
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

open Classical in
noncomputable def genDataC
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (env₀ : Environment) (E : ConstantInfo) : Option (GenData dataOf E (structEnv env₀)) :=
  if h : ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
      dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true
  then some ⟨h.choose, h.choose_spec.2.2, h.choose_spec.1, h.choose_spec.2.1⟩ else none

theorem genDataC_isSome_iff (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (env₀ : Environment) (E : ConstantInfo) :
    (genDataC dataOf env₀ E).isSome = true ↔
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
        dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true := by
  unfold genDataC
  by_cases h : ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
      dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true
  · rw [dif_pos h]
    simp only [Option.isSome_some, true_iff]
    exact h
  · rw [dif_neg h]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact h

theorem reachCover_iff_sdw {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} →
      GenData dataOf E (structEnv env₀) → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).d = g.d)
    (Reach : Name → Prop) :
    ReachCover (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d)
        (genDataC dataOf env₀) ordCallees genSem hmem hev hloc hdecl hd) Reach ↔
      ∀ c, Reach c → ∃ E : ConstantInfo, entry₀ env₀ c = some E ∧
        ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
          dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true := by
  constructor
  · intro H c hc
    obtain ⟨E, g, hE, hg⟩ := H c hc
    refine ⟨E, hE, ?_⟩
    exact (genDataC_isSome_iff dataOf env₀ E).1 (by
      show (genDataC dataOf env₀ E).isSome = true
      rw [show genDataC dataOf env₀ E = some g from hg]; rfl)
  · intro H c hc
    obtain ⟨E, hE, hs⟩ := H c hc
    have hsome := (genDataC_isSome_iff dataOf env₀ E).2 hs
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hsome
    exact ⟨E, g, hE, hg⟩

theorem peel_of_machineShape {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ d : DefinitionVal, E = .defnInfo d ∧
      ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
        mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) := by
  unfold machineShape? at h
  cases E with
  | defnInfo d =>
    refine ⟨d, rfl, ?_⟩
    have hc : ((false : Bool) || !([] : List (String × Nat)).isEmpty) = false := rfl
    rw [hc] at h
    rcases hp : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) with _ | ⟨bs, e⟩
    · simp only [hp] at h
      cases h
    · exact ⟨bs, e, rfl⟩
  | _ => cases h

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.genDataC
#print axioms Tools.ShippingGen5Acc.genDataC_isSome_iff
#print axioms Tools.ShippingGen5Acc.reachCover_iff_sdw
#print axioms Tools.ShippingGen5Acc.peel_of_machineShape
