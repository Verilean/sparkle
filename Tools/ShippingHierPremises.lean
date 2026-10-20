import Tools.ShippingHierPremisesBase
import Tools.ShippingHierTyped

/-! # The combinational route's checker

`shipsHierHCheck`: the facts common to both instance routes
(`Tools.ShippingHierPremisesBase.hierCheck`), local children of the shipped
module and a width-typed body — what `machine_ships_hierH` needs of a run's
modules. -/
namespace Tools.ShippingHierPremises
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked
open Tools.ShippingHierPremisesBase

/-- The checker of the combinational route (`machine_ships_hierH`): the
common facts, local children of the shipped module, a width-typed body. -/
def shipsHierHCheck (ms : List Module) (b : Module) : Bool :=
  hierCheck (childMap ms) b && Tools.ShippingHierOptRunH.kidsLocal ms (checkedOptimize b).body &&
    Tools.ShippingHierTyped.hierTyped (childMap ms) b

theorem shipsHierHCheck_sound {ms : List Module} {b : Module}
    (h : shipsHierHCheck ms b = true) :
    HierFacts (childMap ms) b ∧
      Tools.ShippingHierOptRunH.kidsLocal ms (checkedOptimize b).body = true ∧
      Tools.ShippingHierTyped.hierTyped (childMap ms) b = true := by
  simp only [shipsHierHCheck, Bool.and_eq_true] at h
  exact ⟨hierCheck_sound h.1.1, h.1.2, h.2⟩

end Tools.ShippingHierPremises
