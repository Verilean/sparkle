import Tools.ShippingGen5AccDataAgree
set_option autoImplicit false
-- NOT BUILT: committed tree not yet built (freeze scripts/gen5/DG_ACC_FREEZE_REV10.md rev10 d7f700fc design approved). No sorry / axiom / native_decide.

/-! # DG-ACC unit A10: `genData₀_dataOf` from `GenData`-shaped evidence (scripts/gen5/DG_ACC_FREEZE_REV10.md §1)

PROVED here (conditionally): the kit field `genData₀_dataOf` follows from `GDEvidence` (the fields `hshape`, `hdata` of DG-SEM's frozen
`GenData E senv`, stated for an abstract replacement-point type), and `KitAgrees K f` follows from the equation `K.dataOf = f`.
`GDEvidence` is a hypothesis on ALL `GD` elements: it is conditional glue, NOT a supply of a real `GenData`, a real kit, or of success of `genData₀`.

LIMITS: no kit instance, no `GenData`, `GenWF`, `genSem*`; `hf` / `hK` for any real function or kit, `K.dataOf = dataOfAt`, L, C', `ReachCover`,
any real run are NOT supplied. INTEGRATION OBLIGATION (kept open): at the integration SHA close `hev` from `GenData.hshape/hdata`,
`hf` from `dataOfAt_sound`, `hK` from the real kit's `dataOf` field. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

/-- What `GenData E senv` carries (fields `hshape`, `hdata`), for an abstract replacement-point type. -/
def GDEvidence (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData) (env₀ : Environment) : Prop :=
  ∀ (E : ConstantInfo) (g : GD E),
    machineShape? false [] E (structEnv env₀) = some (dOf g).shape ∧
    dataOf E (structEnv env₀) (dOf g).shape = some (dOf g)

/-- The kit field `genData₀_dataOf`, from the evidence. -/
theorem genData₀_dataOf_of_evidence
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (hev : GDEvidence dataOf GD dOf env₀) :
    ∀ {E g}, genData₀ E = some g →
      ((machineShape? false [] E (structEnv env₀)).bind (dataOf E (structEnv env₀))) = some (dOf g) := by
  intro E g _
  obtain ⟨h1, h2⟩ := hev E g
  rw [h1]
  exact h2

/-- `KitAgrees` from the pointwise-function equation of the kit's field. -/
theorem kitAgrees_of_eq (K : AssignKit ι dom env₀)
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) (h : K.dataOf = f) : KitAgrees K f :=
  fun E se s => by rw [h]

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.genData₀_dataOf_of_evidence
#print axioms Tools.ShippingGen5Acc.kitAgrees_of_eq
