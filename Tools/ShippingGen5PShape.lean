-- Gen5 port of Tools.ShippingGen4Shape (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen5PFPost
import Tools.ShippingGen5PParamBridgeLegal
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

theorem specDesign_eq_addModule {M : Sparkle.IR.AST.Module} {D : Design}
    (h : ∀ x ∈ D.modules, x.name ≠ M.name) : SpecDesign M D = D.addModule M := by
  unfold SpecDesign
  have : (D.modules.any (·.name == M.name)) = false := by
    rw [List.any_eq_false]
    intro x hx hb
    exact h x hx (by simpa using hb)
  rw [this]; rfl

theorem specDesign_keys {M₁ M₂ : Sparkle.IR.AST.Module} {D₁ D₂ : Design}
    (hMn : M₁.name = M₂.name) (hMp : M₁.parameters = M₂.parameters)
    (hp : D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters))
    (hn : D₁.modules.map (·.name) = D₂.modules.map (·.name)) :
    (SpecDesign M₁ D₁).modules.map (·.parameters) = (SpecDesign M₂ D₂).modules.map (·.parameters) ∧
    (SpecDesign M₁ D₁).modules.map (·.name) = (SpecDesign M₂ D₂).modules.map (·.name) := by
  have hany : D₁.modules.any (·.name == M₁.name) = D₂.modules.any (·.name == M₂.name) := by
    have := congrArg (fun l => l.any (· == M₁.name)) hn
    simpa [List.any_map, Function.comp_def, hMn] using this
  unfold SpecDesign
  rw [hany]
  split
  · exact ⟨hp, hn⟩
  · simp [Design.addModule, hp, hn, hMn, hMp]

/-- `fpost_run` with the top-module name of the design as well (same proof, one more `rfl`). -/
theorem fpost_run_top {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters)
      mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      M'.parameters = M.parameters ∧ M'.name = M.name ∧
      D'.modules.map (·.parameters) = D.modules.map (·.parameters) ∧
      D'.modules.map (·.name) = D.modules.map (·.name) ∧ D'.topModule = D.topModule := by
  unfold synthesizeCombinationalWithParameters at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  have hd := topMap_keys Sparkle.IR.ZeroWidth.dropZeroWidthModule M.name
    Tools.ShippingMachineDepthRun.dropZW_name dropZW_parameters D.modules
  have hm := topMap_keys Sparkle.IR.RefineCheck.mergeChecked M.name
    Tools.ShippingMachineDepthRun.mergeChecked_name mergeChecked_parameters
    (D.modules.map fun x => if x.name == M.name then Sparkle.IR.ZeroWidth.dropZeroWidthModule x else x)
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact ⟨dropZW_parameters M, Tools.ShippingMachineDepthRun.dropZW_name M, hd.1, hd.2, rfl⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    refine ⟨?_, ?_, ?_, ?_, rfl⟩
    · exact (mergeChecked_parameters _).trans (dropZW_parameters M)
    · exact (Tools.ShippingMachineDepthRun.mergeChecked_name _).trans
        (Tools.ShippingMachineDepthRun.dropZW_name M)
    · exact hm.1.trans hd.1
    · exact hm.2.trans hd.2

theorem shape_run {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters)
      mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      (SpecDesign M' D').topModule = D.topModule ∧
      (SpecDesign M' D').modules.map (·.parameters) = (SpecDesign M D).modules.map (·.parameters) ∧
      (SpecDesign M' D').modules.map (·.name) = (SpecDesign M D).modules.map (·.name) ∧
      (∀ θ, LegalBinding (SpecDesign M' D') θ ↔ LegalBinding (SpecDesign M D) θ) ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) →
        SpecDesign M' D' = D'.addModule M' ∧ SpecDesign M D = D.addModule M) := by
  obtain ⟨M, D, w1, hcore, hMp, hMn, hp, hn, ht⟩ := fpost_run_top h
  obtain ⟨k1, k2⟩ := specDesign_keys hMn hMp hp hn
  refine ⟨M, D, w1, hcore, ?_, k1, k2, fun θ => legalBinding_congr k1 k2, fun hf => ?_⟩
  · unfold SpecDesign
    split <;> simp [Design.addModule, ht]
  · have hf' : ∀ x ∈ D'.modules, x.name ≠ M'.name := by
      intro x hx
      have hx' : x.name ∈ D.modules.map (·.name) := hn ▸ List.mem_map_of_mem hx
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx'
      rw [hMn, ← hyx]
      exact hf y hy
    exact ⟨specDesign_eq_addModule hf', specDesign_eq_addModule hf⟩

end Tools.ShippingGen4Shape
