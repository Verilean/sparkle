import Tools.ShippingGen4ParamEntry
import Tools.ShippingGen2Defs
import Tools.ShippingDesignWriterRun
set_option autoImplicit false
-- BUILT: clean issue-linked build par9v-38e1f06f (Tests.Gen4.ParamIfaceCheck) exit 0, 705 jobs, approved at 38e1f06f. Comment-only update.

/-! # M4 parametric entry, rev4 §11.3 / §11.5: I4-struct and the pure definitions (scripts/gen4/PARAMETRIC_FREEZE.md)

* `synthesizeCombinationalWithParameters_designTop` (I4-struct): a returning run of the parametric full entry is a
  returning run of the symbolic core followed by the two post-processing steps. It says WHICH `b` can come out of
  WHICH `raw`; it does NOT say that `b` behaves like `raw` (no equivalence, no soundness of the passes).
* `TopIface`, `SrcAt`, `CombTopRunN`, `SpecOk`, `LegalBinding`, `ParamTopShips`, `SpecSuccessAllPositive`,
  `PostTransfer`: DEFINITIONS only. No claim that `SrcAt` is satisfiable for any declaration, that `PostTransfer`
  holds, or that specialization succeeds for any binding. `PostTransfer`, S1-S5, `EntryShips` are UNSUPPLIED.
* `LegalBinding D θ` is literally `validateBindings D.modules θ = .ok ()`, where `validateBindings` is file-private;
  it is named by its mangled constant (as I5a does for `specializeModuleUnchecked`): no production edit, no
  visibility change, no local re-specification to be matched. `specializeDesign_ok_legal` checks that a successful
  specialization implies legality. -/

namespace Tools.ShippingGen4ParamIface
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness
open Tools.ShippingGen4ParamEntry (Tsyn except_bind_ok')

/-! ## I4-struct -/

theorem synthesizeCombinationalWithParameters_designTop {declName : Name}
    {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinationalWithParameters declName parameters)
      mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      D'.topModule = D.topModule ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules) := by
  unfold synthesizeCombinationalWithParameters at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact ⟨Or.inl rfl, rfl,
      fun hx => Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    refine ⟨Or.inr rfl, rfl, fun hx => ?_⟩
    show (D.modules.map _).map _ = _
    rw [Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx,
      Tools.ShippingKidsChildIface.map_other M.name _ D.modules hx]

/-! ## The private `validateBindings`, named by its mangled constant -/

open Lean Elab Term in
/-- `specValidateBindings ms θ` is the file-private `Sparkle.IR.Specialize.validateBindings ms θ`. -/
elab "specValidateBindings " ms:term:max bs:term:max : term => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.validateBindings
  let modTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``Sparkle.IR.AST.Module)
  let ms ← elabTerm ms (some modTy)
  let bs ← elabTerm bs (some (mkConst ``Sparkle.IR.Specialize.Bindings))
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.mkAppM n #[ms, bs]

/-! ## Definitions (no claim) -/

/-- The interface DATA of A-COMB (GEN2_DEFS.lean.txt:60-74); `seq` of the rev1 sketch is dropped (unused). -/
structure TopIface where
  bsC   : List (Name × MixedGateBinder)
  outsC : List Sparkle.IR.Machine.OutField
  S     : (Nat → List Nat) → List (Nat → Nat)

/-- The source at a binding: per declaration. A PREMISE of the same kind as G3, not a derived object. -/
abbrev SrcAt := List (String × Nat) → TopIface

/-- A parametric top at depth `n`, after specialization: the A-COMB combinational child run. -/
def CombTopRunN (D' : Design) (n : Nat) (b' : Sparkle.IR.AST.Module) (I : TopIface) : Prop :=
  Tools.ShippingGen2.CombChildRunN (Tools.ShippingMachineLinked.childMap D'.modules) D' n b'
    I.bsC I.outsC I.S

/-- What `validateBindings` accepts (names are design-global). -/
def LegalBinding (D : Design) (θ : List (String × Nat)) : Prop :=
  specValidateBindings D.modules θ = .ok ()

def SpecOk (D : Design) (θ : List (String × Nat)) : Prop :=
  ∃ D', Sparkle.IR.Specialize.specializeDesign D θ = .ok D'

/-- The guarantee for the parametric disjunct. Success is a HYPOTHESIS here. -/
def ParamTopShips (b : Sparkle.IR.AST.Module) (D : Design) (src : SrcAt) : Prop :=
  ∀ θ, LegalBinding (D.addModule b) θ →
    ∀ D', Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →
      ∃ n b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' (src θ)

/-- Separate supply obligation (target kept, not narrowed; see PARAMETRIC_SPECSUCCESS_DECISION.md): every legal
binding specializes, GIVEN that the design's top module is present (`specializeDesign` checks that before
`validateBindings`, so legality alone cannot imply success). Not claimed for any declaration here. -/
def SpecSuccessAllPositive (b : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ((D.addModule b).findModule (D.addModule b).topModule).isSome = true →
    ∀ θ, LegalBinding (D.addModule b) θ → SpecOk (D.addModule b) θ

/-- The interface-level transfer from the raw translator module to the post-processed one (UNSUPPLIED: a
proposition to be proved per post-processing outcome, never assumed). -/
def PostTransfer (raw b : Sparkle.IR.AST.Module) (Dr D : Design) (I : TopIface) : Prop :=
  ∀ (θ : List (String × Nat)) (Dr' D' : Design),
    Sparkle.IR.Specialize.specializeDesign (Dr.addModule raw) θ = .ok Dr' →
    Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →
    ∀ (n : Nat) (raw' : Sparkle.IR.AST.Module), Dr'.findModule raw.name = some raw' →
      CombTopRunN Dr' n raw' I →
      ∃ b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' I

/-! ## A successful specialization is a legal one -/

theorem specializeDesign_ok_legal {design D' : Design} {θ : List (String × Nat)}
    (h : Sparkle.IR.Specialize.specializeDesign design θ = .ok D') :
    LegalBinding design θ := by
  unfold Sparkle.IR.Specialize.specializeDesign at h
  by_cases hn : (design.findModule design.topModule).isNone = true
  · simp only [hn, ↓reduceIte] at h
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · have hn' : (design.findModule design.topModule).isNone = false := Bool.eq_false_iff.mpr hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨u, hu, -⟩ := except_bind_ok' h
    cases u
    exact hu

end Tools.ShippingGen4ParamIface
