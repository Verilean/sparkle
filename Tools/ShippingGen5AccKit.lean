import Tools.ShippingGen5AccRouteR
import Tools.ShippingGen5AccGenDataKit
import Tools.ShippingGen5AccOrdCallees
set_option autoImplicit false
-- NOT BUILT (scripts/gen5/AC9KIT_FREEZE.md). No sorry / axiom / native_decide.

/-! # C.AC-9 assembled: the Acc kit fixed to `mkKit (dataOfAt lvl) …` (scripts/gen5/AC9KIT_FREEZE.md)

`accServed0_of_cover_gatesK` is `accServed0_of_cover_gatesR` at `K := mkKit (dataOfAt lvl) (GenData …) … ` (ASSEMBLY_COST §1.1);
`hK` is `mkKit_dataOf` (`rfl`), so neither `hDS` nor `hK` is a binder. New binders: `lvl`, `initsOf`, `hs : DataOfSound (dataOfAt lvl) initsOf`
(the existing row C.SM-1), `genData₀` (a non-Prop carrier). -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

local macro "accKit%" : term =>
  `(mkKit (Tools.ShippingGen5DataOf.dataOfAt lvl) (fun E => GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env₀))
    (fun {E} g => g.d) genData₀ ordCallees₀ (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
    (genData_gdEvidence _) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs))

theorem accServed0_of_cover_gatesK (lvl : Lean.Expr → Nat)
    {initsOf : (d : MachineData) → HList (Tools.ShippingMachineDenote.tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env₀)))
    (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge (accKit%) X c → Reach c)
    (hcov : ReachCover (accKit%) Reach) (hG : GatesNoneAt env₀ Reach)
    (hC : ClosesOfShape env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach) :
    AccServed0Stmt (accKit%) L Reach :=
  accServed0_of_cover_gatesR (accKit%) L Reach lvl hcl hcov (mkKit_dataOf _ _ _ _ _ _ _ _ _ _ _) hG hC hRS

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.accServed0_of_cover_gatesK
