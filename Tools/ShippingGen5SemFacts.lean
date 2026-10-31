import Tools.ShippingGen5SemCausal
set_option autoImplicit false
-- Pod incremental build (kjob lake build Tools.ShippingGen5SemFacts) exit 0 on the content of a00f8017 (Lean/lakefile identical to the commit); clean issue-linked build is the coder's. No sorry/axiom/native_decide.
/-! # DG-SEM U6B (scripts/gen5/DG_SEM_FREEZE_P6D.md §3): `genFacts_gen`, `genFacts_comb`, `genFacts`

`FactsOf (genSemI Q X g)`: the `.gen` arm (`GenFacts`, conditional on `CalleesCausal Q g.d` for its `causal` field only, through
`extCausal_of_genSem`) and the `.comb` arm (`CombFacts`, no causality hypothesis). Nothing here supplies `hp`/`hq`/`GenIn` of a run,
`CalleesCausal` for a real table, `GenSFacts`, ACC, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource

variable {ι : Type} {dom : ι → DomainConfig}

theorem hlist_nil_subsingleton (ss : List Tools.ShippingUnifiedSource.SType) (h : ss = []) (x y : HList (tys ss)) : x = y := by
  subst h
  rfl

theorem genFacts_gen (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d)
    (s : SrcSem ι dom) (hs : genSemI Q X g = SemPkg.gen s) :
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src := by
  unfold genSemI at hs
  split at hs
  · cases hs
  · injection hs with h
    subst h
    exact @Tools.ShippingQuadComposed.GenFacts.mk _ _ _ _ (genSemGen Q X g).inh _ _ _ _ _ _ g.ok g.bodyEq g.init (genSemGenE_writes X g (extBOf Q g) (extOf Q g))
      (genSemGenE_result X g (extBOf Q g) (extOf Q g)) (genSemGenE_source X g (extBOf Q g) (extOf Q g))
      (extCausal_of_genSem Q g hQ)

theorem genFacts_comb (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : CombSem ι dom) (hs : genSemI Q X g = SemPkg.comb s) :
    Tools.ShippingGen2.CombFacts s.d dom s.inits s.src := by
  unfold genSemI at hs
  split at hs
  · rename_i hc
    injection hs with h
    subst h
    have hss : g.d.ss = [] := by
      have := (Bool.and_eq_true _ _).mp hc |>.1
      exact List.isEmpty_iff.mp this
    exact
      { ok := g.ok
        hbody := g.bodyEq
        hinit := g.init
        hnext := fun i bools bits t => hlist_nil_subsingleton g.d.ss hss _ _
        hres := fun i bools bits t => by
          show List.map _ (List.map _ _) = _
          rw [List.map_map]
          rfl }
  · cases hs

theorem genFacts (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    FactsOf (genSemI Q X g) := by
  unfold genSemI
  split
  · exact genFacts_comb Q X g _ (by unfold genSemI; simp_all)
  · exact genFacts_gen Q X g hQ _ (by unfold genSemI; simp_all)

end Tools.ShippingGen5Sem
