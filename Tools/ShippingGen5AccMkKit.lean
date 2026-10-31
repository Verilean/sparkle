import Tools.ShippingGen5AccGenDataEv
set_option autoImplicit false
-- NOT BUILT. Lean source for DG-ACC unit A11 (freeze scripts/gen5/DG_ACC_FREEZE_REV11.md, design approved at 8e0d0bc3). No sorry / axiom / native_decide.

/-! # DG-ACC unit A11: the kit built from abstract parts, with `dataOf := f` (scripts/gen5/DG_ACC_FREEZE_REV11.md §1)

PROVED here (conditionally): `mkKit` builds an `AssignKit` from abstract parts (`GD`, `dOf`, `genData₀`, `ordCallees`, `genSem` and their laws as
hypotheses), with `dataOf := f` and `genData₀_dataOf` filled by A10; hence `(mkKit ..).dataOf = f`, `KitAgrees (mkKit ..) f` and, given `hf : DataSoundAt f`,
`DataSound (mkKit ..)`.

LIMITS: no real `GD` / `genData₀` / `genSem`, no `GenData`, `GenWF`, success of `genData₀`; `hev`, `hf` for any real function, L, C', `ReachCover`,
any real run, M5, FG are NOT supplied. INTEGRATION OBLIGATION (kept open): instantiate the parts from DG-SEM's `GenData` / `genSem`, close `hev`
(from `GenData.hshape/hdata`) and `hf` (from `dataOfAt_sound`). Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

def mkKit
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g) :
    AssignKit ι dom env₀ :=
  { dataOf := f, GD := GD, dOf := dOf, genData₀ := genData₀, ordCallees := ordCallees, genSem := genSem,
    mem_ordCallees := hmem,
    genData₀_dataOf := genData₀_dataOf_of_evidence f GD dOf genData₀ hev,
    genSem_local := hloc, genSem_decl := hdecl, genSem_d := hd }

theorem mkKit_dataOf
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g) :
    (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd).dataOf = f := rfl

theorem mkKit_agrees
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g) :
    KitAgrees (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) f :=
  kitAgrees_of_eq (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) f rfl

theorem mkKit_dataSound
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : DataSoundAt f) :
    DataSound (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) :=
  dataSound_of_agree (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) f hf
    (mkKit_agrees f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd)

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.mkKit
#print axioms Tools.ShippingGen5Acc.mkKit_dataOf
#print axioms Tools.ShippingGen5Acc.mkKit_agrees
#print axioms Tools.ShippingGen5Acc.mkKit_dataSound
