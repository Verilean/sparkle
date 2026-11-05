import Tools.ShippingGen5AccServed
import Tools.ShippingGen5DataOfDims
set_option autoImplicit false
-- NOT BUILT (skeleton; build result is added by a comment-only commit). No sorry / axiom / native_decide.

/-! # C.AC-9: `accServed0_of_cover` with the carrier fixed to `dataOfAt lvl` (`scripts/gen5/AC9CV5_FREEZE.md`)

`hDS : DataOfShape K` is derived from `dataOfAt_dims` (`.1`) once `K.dataOf = dataOfAt lvl` (`hK`, the carrier fixing).
`hK` is the carrier fixing (it holds by `rfl` for a kit built by `mkKit (dataOfAt lvl) …`, `mkKit_dataOf`). The conclusion is that of `accServed0_of_cover`.
Not supplied: `DataSound` / `GDEvidence` for a real kit, `ReachCover`, `ReadsSupplyAt`, `RunDataLink` (not a premise of the cover form). -/
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem dataOfShape_of_dataOfAt (K : AssignKit ι dom env₀) (lvl : Lean.Expr → Nat)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl) : DataOfShape K := by
  intro E se s d hd
  rw [hK] at hd
  exact (Tools.ShippingGen5DataOf.dataOfAt_dims lvl hd).1

theorem accServed0_of_coverR (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop)
    (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl)
    (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach :=
  accServed0_of_cover K L Reach hcl hRoute hcov (dataOfShape_of_dataOfAt K lvl hK) hRS

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.dataOfShape_of_dataOfAt
#print axioms Tools.ShippingGen5Acc.accServed0_of_coverR
