import Tools.ShippingGen5SemFacts
import Tools.ShippingMachineCausalCtx
set_option autoImplicit false
-- Clean issue-linked build smu13v-343faecd exit 0 (716 jobs), approved at 343faecd (U6C; conditional on hQ). Kernel type/value audit only, not an audit of opaque implementations or compiled code. No sorry/axiom/native_decide.
/-! # DG-SEM U6C (scripts/gen5/DG_SEM_FREEZE_P6E.md §3, §5): `extJoint_of_genSem`, `genSemGen_srcCausal`, `genSemComb_srcCausal`, `genSemI_srcCausal`

The step `SrcCausal (genSemI Q X g)` from `CalleesCausal Q g.d`. The `.gen` arm builds the arguments of
`Tools.ShippingMachineCausal.src_causal_of_data_causal` directly (no `genFacts_gen`, whose `hs` need not hold when `genSemI` selects
`comb`). Conditional on `hQ : CalleesCausal Q g.d` for the `.gen` arm only. Nothing here supplies `CalleesCausal` for a real table,
`GenSFacts`, `Acc`, `hp`/`hq`/`GenIn` of a run, M5 or FG; `g.wf` stays a field of `GenIn` (not claimed wf-free). -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineCausal (Ctx CtxAgree)

variable {ι : Type} {dom : ι → DomainConfig}

theorem ExtStage_causal2 (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (bools bools' : Nat → Signal (dom i) Bool) (bits bits' : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c)
    (hB : ∀ c, c ≤ t → (∀ p, (bools p).val c = (bools' p).val c) ∧ ∀ p w, (bits p w).val c = (bits' p w).val c) :
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools' bits' S' n).1 p).val t) ∧
    (∀ p w, ((ExtStage Q g i bools bits S n).2 p w).val t = ((ExtStage Q g i bools' bits' S' n).2 p w).val t) := by
  induction n generalizing t with
  | zero => exact hB t (Nat.le_refl t)
  | succ n ih =>
    rw [ExtStage_succ, ExtStage_succ]
    exact callOut_causal Q g hQ i S S' n t _ _ hS fun c hc =>
      ih c (fun c' hc' => hS c' (Nat.le_trans hc' hc)) (fun c' hc' => hB c' (Nat.le_trans hc' hc))

theorem map_apply_eq_of_getElem (l l' : List (Nat → Nat)) (t : Nat) (hlen : l.length = l'.length)
    (h : ∀ (k : Nat) (f f' : Nat → Nat), l[k]? = some f → l'[k]? = some f' → f t = f' t) :
    l.map (fun f => f t) = l'.map (fun f => f t) := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_map]
  by_cases hn : n < l.length
  · have hn' : n < l'.length := by omega
    have h1 : l[n]? = some l[n] := List.getElem?_eq_getElem hn
    have h2 : l'[n]? = some l'[n] := List.getElem?_eq_getElem hn'
    rw [h1, h2]
    exact congrArg some (h n _ _ h1 h2)
  · have h1 : l[n]? = none := List.getElem?_eq_none (by omega)
    have h2 : l'[n]? = none := List.getElem?_eq_none (by omega)
    rw [h1, h2]

theorem extJoint_of_genSem (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    ∀ (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
      (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val t) ∧
      (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t) := by
  intro i x x' t h
  have := ExtStage_causal2 Q g hQ i x.B x'.B x.V x'.V x.S x'.S g.d.shape.insts.length t h.2.2
    (fun c hc => ⟨fun p => h.1 p c hc, fun p w => h.2.1 p w c hc⟩)
  exact ⟨this.2, this.1⟩

theorem genSemGen_src_length (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (i : ι)
    (A : Nat → Signal (dom i) Bool) (B : (j n : Nat) → Signal (dom i) (BitVec n)) :
    ((genSemGen Q X g).src i A B).length = g.d.outs.length := by
  have h := genSemGenE_result X g (extBOf Q g) (extOf Q g) i A B
    (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBodyE g (extBOf Q g) (extOf Q g) i A B)) 0
  have h2 := congrArg List.length h
  rw [List.length_map, List.length_map] at h2
  exact h2

theorem genSemGen_srcCausal (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    SrcCausal (SemPkg.gen (genSemGen Q X g)) := by
  intro i A A' B B' t h
  show ((genSemGen Q X g).src i A B).map (fun f => f t) = ((genSemGen Q X g).src i A' B').map (fun f => f t)
  refine map_apply_eq_of_getElem _ _ t
    ((genSemGen_src_length Q X g i A B).trans (genSemGen_src_length Q X g i A' B').symm) ?_
  exact @Tools.ShippingMachineCausal.src_causal_of_data_causal X g.d ι dom ⟨g.inits⟩ (fun _ => List (Nat → Nat)) g.inits
    (refBodyE g (extBOf Q g) (extOf Q g)) (fun _ r => r) (extOf Q g) (extBOf Q g) (genSemGen Q X g).src
    g.ok g.bodyEq g.init
    (genSemGenE_writes X g (extBOf Q g) (extOf Q g))
    (genSemGenE_result X g (extBOf Q g) (extOf Q g))
    (genSemGenE_source X g (extBOf Q g) (extOf Q g))
    (extCausal_of_genSem Q g hQ)
    (extJoint_of_genSem Q g hQ)
    i A A' B B' t (fun p c hc => (h c hc).1 p) (fun p n c hc => (h c hc).2 p n)

theorem genSemComb_srcCausal (X : Name) (g : GenIn) :
    SrcCausal (SemPkg.comb (genSemComb (ι := ι) (dom := dom) X g)) := by
  intro i A A' B B' t h
  have hb := (h t (Nat.le_refl t)).1
  have hv := (h t (Nat.le_refl t)).2
  show (List.map (fun f => f t) ((genSemComb (ι := ι) (dom := dom) X g).src i A B)) = _
  have key := Tools.ShippingMachineCausal.typedVal_congrB g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls A A' B B' t g.inits hb hv
  simp only [genSemComb, SemPkg.src, List.map_map, Function.comp_def, key]

theorem genSemI_srcCausal (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) :
    SrcCausal (genSemI Q X g) := by
  unfold genSemI
  split
  · exact genSemComb_srcCausal X g
  · exact genSemGen_srcCausal Q X g hQ

end Tools.ShippingGen5Sem
