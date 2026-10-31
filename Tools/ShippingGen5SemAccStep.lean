import Tools.ShippingGen5SemSrcCausal
set_option autoImplicit false
-- NOT BUILT (U6D, scripts/gen5/DG_SEM_FREEZE_P6F.md; clean build is run by the coder). No sorry/axiom/native_decide.
/-! # DG-SEM U6D (scripts/gen5/DG_SEM_FREEZE_P6F.md §3): `srcCausal_of_acc_unfold`, `factsOf_of_acc_unfold`, `factsOf_all_of_acc_unfold`

Abstract `Acc` induction over an arbitrary relation `R` and table `G`. `hunf` is a premise about the table (not a law); `R` is any
relation containing the ordinary-edge pairs. Nothing here supplies `hunf`/`hacc` for the real `genS`, `GenData.toIn`, a run, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

theorem srcCausal_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s) :
    SrcCausal s := by
  induction hX generalizing s with
  | intro Y hY ih =>
    obtain ⟨g, hg, hedge⟩ := hunf Y s (Acc.intro Y hY) hs
    subst hg
    exact genSemI_srcCausal G Y g fun k hk s' hs' => ih _ (hedge k hk) s' hs'

theorem factsOf_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s) :
    FactsOf s := by
  obtain ⟨g, hg, hedge⟩ := hunf X s hX hs
  subst hg
  exact genFacts G X g fun k hk s' hs' =>
    srcCausal_of_acc_unfold R G hunf _ (Acc.inv hX (hedge k hk)) s' hs'

theorem factsOf_all_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (hacc : ∀ (Y : Name) (s : SemPkg ι dom), G Y = some s → Acc R Y) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s :=
  fun X s hs => factsOf_of_acc_unfold R G hunf X (hacc X s hs) s hs

end Tools.ShippingGen5Sem
