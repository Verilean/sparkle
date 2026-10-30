set_option autoImplicit false
-- Built at 5e3ebf90bf3807120dd58f86b3b4f8714fe7835a (kjob lake build Tests.Gen5.DeclConnectAbsCheck, exit 0, 4 jobs): U1-U6 and checks. Axioms: none beyond core (all []). Abstract interface only; not DG-SEM/DATAOF/ACC results.

/-! # DC-CONNECT abstract units U1-U6 (scripts/gen5/DC_CONNECT_FREEZE.md rev2 §4)

`DeclConnect` over an ABSTRACT interface: the environment `E`, names `N`, constants `CI`, packages `Pk`, and the shape/adapter
data are PARAMETERS (`Shape`, `Ty`, `shapeOf`, `Match`, `Obs`). Nothing here mentions `Pkg`, `MachineData`, `sigShape?`,
`ConstantInfo`, or any dependency (DG-SEM/DATAOF/ACC). The concrete instance is a later file. No sorry/axiom/native_decide. -/
namespace Tools.ShippingGen5DeclConnectAbs

universe u
variable {E N CI : Type} {Pk : Type u} {Shape : Type} {Ty : Shape → Type}

/-- Functionality (V2) of an abstract constant-value relation. -/
def Functional (CV : E → N → (α : Type) → α → Prop) : Prop :=
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w

/-- `DeclConnect` at one name (existence of constant, shape, value; shape matches; value's observation equals the package's). -/
def DCAt (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (X : N) : Prop :=
  ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
    find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v

/-- `DeclConnect`: uniform over the targets. -/
def DCGen (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E)
    (Tgt : N → Prop) : Prop :=
  ∀ X, Tgt X → DCAt find CV shapeOf Match Obs P env X

/-- The implication form (INTERMEDIATE; true for the empty relation). -/
def DCImp (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E)
    (Tgt : N → Prop) : Prop :=
  ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p →
    ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v

section
variable (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
  (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E)

-- U1
theorem dcGen_iff (Tgt : N → Prop) :
    DCGen find CV shapeOf Match Obs P env Tgt ↔ ∀ X, Tgt X → DCAt find CV shapeOf Match Obs P env X := Iff.rfl

-- U2
theorem dcGen_mono {Tgt Tgt' : N → Prop} (h : ∀ X, Tgt' X → Tgt X) :
    DCGen find CV shapeOf Match Obs P env Tgt → DCGen find CV shapeOf Match Obs P env Tgt' :=
  fun H X hX => H X (h X hX)

-- U3a
theorem dcImp_of_empty (Tgt : N → Prop) :
    DCImp find (fun _ _ _ _ => False) shapeOf Match Obs P env Tgt := by
  intro X _ p _ ci _ sh _ _ v hv
  exact hv.elim

-- U3b
theorem not_dcGen_of_empty (Tgt : N → Prop) {X : N} {p : Pk} (hT : Tgt X) (hP : P X = some p) :
    ¬ DCGen find (fun _ _ _ _ => False) shapeOf Match Obs P env Tgt := by
  intro H
  obtain ⟨_, _, v, _, _, _, hcv, _⟩ := H X hT p hP
  exact hcv

-- U4a
theorem dcImp_of_dcGen (hV2 : Functional CV) (Tgt : N → Prop) :
    DCGen find CV shapeOf Match Obs P env Tgt → DCImp find CV shapeOf Match Obs P env Tgt := by
  intro H X hX p hP ci hci sh hsh hm v hv
  obtain ⟨ci₀, sh₀, v₀, hf₀, hs₀, _, hcv₀, hobs₀⟩ := H X hX p hP
  have hc : ci₀ = ci := Option.some.inj (hf₀.symm.trans hci)
  subst hc
  have hs : sh₀ = sh := Option.some.inj (hs₀.symm.trans hsh)
  subst hs
  obtain ⟨_, hv'⟩ := hV2 env X _ _ v₀ v hcv₀ hv
  have : v₀ = v := eq_of_heq hv'
  subst this
  exact hobs₀

-- U4b
theorem dcGen_of_imp_exists (Tgt : N → Prop) (hImp : DCImp find CV shapeOf Match Obs P env Tgt)
    (hEx : ∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v) :
    DCGen find CV shapeOf Match Obs P env Tgt := by
  intro X hX p hP
  obtain ⟨ci, sh, v, hf, hs, hm, hcv⟩ := hEx X hX p hP
  exact ⟨ci, sh, v, hf, hs, hm, hcv, hImp X hX p hP ci hf sh hs hm v hcv⟩

end

-- U5
theorem acc_ready {α : Sort u} {R : α → α → Prop} {Ready : α → Prop}
    (hstep : ∀ X, (∀ c, R c X → Ready c) → Ready X) : ∀ X, Acc R X → Ready X := by
  intro X hX
  induction hX with
  | intro X _ ih => exact hstep X (fun c hc => ih c hc)

-- U6 (INTERMEDIATE: `hstep` is the unsupplied content of rows 0-4)
theorem dcGen_of_rows (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E)
    (Tgt : N → Prop) {R : N → N → Prop}
    (hAcc : ∀ X, Tgt X → Acc R X) (_hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DCAt find CV shapeOf Match Obs P env c) →
      DCAt find CV shapeOf Match Obs P env X) :
    DCGen find CV shapeOf Match Obs P env Tgt := by
  intro X hX
  have key : ∀ Y, Acc R Y → Tgt Y → DCAt find CV shapeOf Match Obs P env Y := by
    intro Y hY
    induction hY with
    | intro Y _ ih =>
      intro hT
      exact hstep Y hT (fun c hc hTc => ih c hc hTc)
  exact key X (hAcc X hX) hX

end Tools.ShippingGen5DeclConnectAbs
