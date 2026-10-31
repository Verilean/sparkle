import Tools.ShippingGen5AccMkKit
set_option autoImplicit false
-- NOT BUILT (A12, written at a5defa8c; Pod incremental build pending). Lean source for DG-ACC unit A12 (freeze scripts/gen5/DG_ACC_FREEZE_REV12.md, design approved at a5defa8c). No sorry / axiom / native_decide.

/-! # DG-ACC unit A12: a concrete `ordCallees₀` with its membership law `hmem` (scripts/gen5/DG_ACC_FREEZE_REV12.md §1)

PROVED here: `ordCallees₀ d` is the `finRange`-filter of instances whose origin has `child? = none` (`.field` instances included, default `.ord`
via `getD`); `ordCallees₀_mem` is exactly the `hmem` argument of `mkKit`; `mkKit_ordCallees₀_dataSound` instantiates `mkKit_dataSound` with it.

LIMITS: no real `GD` / `genData₀` / `genSem`, no `GenData`, `GenWF`, success of `genData₀`; `hev`, `hf`, L, C', `ReachCover`, real run, M5, FG are NOT
supplied. A12 only fixes `ordCallees` and `hmem`. Not DG-ACC / M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)

def ordCallees₀ (d : MachineData) : List (Fin d.shape.insts.length) :=
  (List.finRange d.shape.insts.length).filter
    (fun k => ((d.shape.instOrigins.getD k .ord).child?).isNone)

theorem ordCallees₀_mem (d : MachineData) (k : Fin d.shape.insts.length) :
    k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? = none := by
  simp [ordCallees₀, List.mem_filter, List.mem_finRange, Option.isNone_iff_eq_none]

theorem mkKit_ordCallees₀_dataSound {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (f : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : ConstantInfo) → Option (GD E))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees₀ (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : DataSoundAt f) :
    DataSound (mkKit f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd) :=
  mkKit_dataSound f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd hf

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.ordCallees₀
#print axioms Tools.ShippingGen5Acc.ordCallees₀_mem
#print axioms Tools.ShippingGen5Acc.mkKit_ordCallees₀_dataSound
