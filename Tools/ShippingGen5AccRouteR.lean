import Tools.ShippingGen5AccRoute
import Tools.ShippingGen5AccServedR
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # C.AC-9 at the top of the Acc chain (scripts/gen5/AC9_FREEZE.md)

`accServed0_of_cover_gates` (Tools/ShippingGen5AccRoute.lean, no consumer: the top of the Acc chain) takes `hDS : DataOfShape K`.
`accServed0_of_cover_gatesR` is the same statement with `hDS` replaced by the carrier fixing `hK : K.dataOf = dataOfAt lvl`;
`DataOfShape K` follows from `dataOfAt_dims` (`dataOfShape_of_dataOfAt`). For a kit built by `mkKit (dataOfAt lvl) …`, `hK` is
`rfl` (`mkKit_dataOf`). Whether `hK` counts as a ledger row is the reviewer's call. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

theorem accServed0_of_cover_gatesR (L : Laws mref cref) (Reach : Name → Prop) (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hcov : ReachCover K Reach) (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl) (hG : GatesNoneAt env₀ Reach)
    (hC : ClosesOfShape env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach :=
  accServed0_of_cover_gates K L Reach hcl hcov (dataOfShape_of_dataOfAt K lvl hK) hG hC hRS

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.accServed0_of_cover_gatesR
