import Tools.ShippingGen5AccHinv
-- NOT BUILT HERE (scripts/gen5/CKIT_FREEZE.md at 7c8fdff7, reviewer design-approved). proof-accept candidate: same frozen types as skeleton 621367d2, bodies filled with existing lemmas. No sorry/axiom/native_decide.

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

theorem genData_gdEvidence
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData) :
    GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀ :=
  fun E g => genData_evidence (structEnv env₀) E g

theorem genData_genSem_decl
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X :=
  fun Q X {_} g => genSemI_decl Q X (g.toIn hs)

theorem genData_genSem_d
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d :=
  fun Q X {_} g => genSemI_d Q X (g.toIn hs)

theorem genData_genSem_local
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g :=
  fun Q Q' X {_} g h => genSemI_local Q Q' X (g.toIn hs) (fun k hk => h k (by
    have hk' : k ∈ ordCallees₀ (g.toIn hs).d := by
      rw [← ordCallees_eq_ordCallees₀]; exact hk
    exact hk'))

theorem factsOf_genS_assembled''
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀))) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)) X = some s →
      FactsOf s :=
  factsOf_genS_assembled' hs genData₀ (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)

end Tools.ShippingGen5Acc
