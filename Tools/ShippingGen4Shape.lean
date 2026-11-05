import Tools.ShippingGen4FPost
import Tools.ShippingGen4ParamBridgeLegal
set_option autoImplicit false

/-! # Shape (scripts/gen4/SHAPE_FREEZE.md): which design `specializeDesign` reads

`SpecDesign` is the `design'` of `synthesizeHierarchicalWithParameters`. `shape_run` relates it to the design of the
core output from a returning run of the parametric entry; `legalBinding_congr` is the transfer of legality along
equal `(name, parameters)` keys. No equivalence claim about the passes; no collision claim (F-top's goal). -/

namespace Tools.ShippingGen4Shape
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness
open Tools.ShippingGen4ParamEntry (Tsyn)
open Tools.ShippingGen4ParamIface (LegalBinding)
open Tools.ShippingGen4FPost (topMap_keys dropZW_parameters mergeChecked_parameters)

open Lean Elab Term in
/-- the file-private `Sparkle.IR.Specialize.validateParameterDeclarations`, by its mangled constant. -/
elab "specValidateDecl " ms:term:max : term => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.validateParameterDeclarations
  let modTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``Sparkle.IR.AST.Module)
  let ms ← elabTerm ms (some modTy)
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.mkAppM n #[ms]

/-- `design'` of `synthesizeHierarchicalWithParameters` (Elab.lean:9128). -/
def SpecDesign (M : Sparkle.IR.AST.Module) (D : Design) : Design :=
  if D.modules.any (·.name == M.name) then D else D.addModule M

/-- Position-wise relation (no `List.Forall₂` in core). -/
inductive Rel2 {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | nil : Rel2 R [] []
  | cons {a b l1 l2} : R a b → Rel2 R l1 l2 → Rel2 R (a :: l1) (b :: l2)

theorem forall2_of_keys : ∀ (l1 l2 : List Sparkle.IR.AST.Module),
    l1.map (·.parameters) = l2.map (·.parameters) → l1.map (·.name) = l2.map (·.name) →
    Rel2 (fun a b => a.name = b.name ∧ a.parameters = b.parameters) l1 l2
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: l1, _ :: l2, hp, hn => by
    simp only [List.map_cons, List.cons.injEq] at hp hn
    exact .cons ⟨hn.1, hp.1⟩ (forall2_of_keys l1 l2 hp.2 hn.2)

theorem forIn_rel {α : Type} {R : α → α → Prop} {l1 l2 : List α} (h : Rel2 R l1 l2)
    (f1 f2 : α → PUnit → Except String (ForInStep PUnit))
    (hf : ∀ a b, R a b → ∀ r, f1 a r = f2 b r) :
    ∀ r : PUnit, forIn l1 r f1 = forIn l2 r f2 := by
  induction h with
  | nil => intro r; rfl
  | cons hab _ ih =>
    intro r
    rw [List.forIn_cons, List.forIn_cons, hf _ _ hab r]
    cases f2 _ r with
    | error e => rfl
    | ok s =>
      cases s with
      | done => rfl
      | yield r' => exact ih r'

theorem legalBinding_congr {D₁ D₂ : Design} {θ : List (String × Nat)}
    (hp : D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters))
    (hn : D₁.modules.map (·.name) = D₂.modules.map (·.name)) :
    LegalBinding D₁ θ ↔ LegalBinding D₂ θ := by
  have hF := forall2_of_keys _ _ hp hn
  have hflat : D₁.modules.flatMap (fun m => m.parameters.map (·.name)) =
      D₂.modules.flatMap (fun m => m.parameters.map (·.name)) := by
    have : ∀ (l1 l2 : List Sparkle.IR.AST.Module), l1.map (·.parameters) = l2.map (·.parameters) →
        l1.flatMap (fun m => m.parameters.map (·.name)) = l2.flatMap (fun m => m.parameters.map (·.name)) := by
      intro l1
      induction l1 with
      | nil => intro l2 h; cases l2 <;> simp_all
      | cons a l1 ih =>
        intro l2 h
        cases l2 with
        | nil => simp at h
        | cons b l2 =>
          simp only [List.map_cons, List.cons.injEq] at h
          simp only [List.flatMap_cons, h.1, ih l2 h.2]
    exact this _ _ hp
  have hdecl : specValidateDecl D₁.modules = specValidateDecl D₂.modules := by
    unfold_priv validateParameterDeclarations
    refine congrArg (fun x => x >>= fun _ => (pure () : Except String Unit)) (forIn_rel hF _ _ ?_ PUnit.unit)
    intro a b hab r
    obtain ⟨h1, h2⟩ := hab
    dsimp only
    simp only [h1, h2]
  have hv : specValidateBindings D₁.modules θ = specValidateBindings D₂.modules θ := by
    unfold_priv validateBindings
    rw [hdecl, hflat]
  unfold LegalBinding
  rw [hv]

end Tools.ShippingGen4Shape
