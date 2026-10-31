import Tools.ShippingGen5AccOrdCallees
import Tools.ShippingGen5SemGenData
-- proof-accept SKELETON: the three roots have the frozen types (scripts/gen5/CANDA_FREEZE.md at eab9da5d) and `sorry` bodies (intended holes).

/-! # Candidate A: `hacc_genS`, `ordCallees_eq_ordCallees₀`, `factsOf_genS_assembled` (scripts/gen5/CANDA_FREEZE.md §2)

PROVED here (conditional parts, carrier fixed to `GenData` / `structEnv env₀` / `ordCallees₀`): `hacc_genS` is the `hacc` argument of `factsOf_all_of_acc_unfold`
(from `genS_some_inv`); `ordCallees_eq_ordCallees₀` connects SEM `ordCallees` with ACC `ordCallees₀`; `factsOf_genS_assembled` feeds `hacc_genS` and
`ordCallees₀_mem` into the assembly, so its hypotheses are only the existing rows C.SM-1 / C.AC-2 / C.AC-3 / C.SM-3.

LIMITS: no supply of `DataOfSound`, `genData₀` success, `GenWF`, `hinv`; C.SM-3, C.AC-8, A.P-24 are not subtracted; no claim for other carriers. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

theorem hacc_genS (K : AssignKit ι dom env₀) :
    ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = some s → Acc (CallRel K) Y := by
  sorry

theorem ordCallees_eq_ordCallees₀ (d : MachineData) : ordCallees d = ordCallees₀ d := by
  sorry

theorem factsOf_genS_assembled
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X gd) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s → FactsOf s := by
  sorry

end Tools.ShippingGen5Acc
