-- Gen5 port of Tools.ShippingGen4FKidsObl (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen5PFKids
import Tools.ShippingGen5PFKidsParams
import Tools.ShippingGen5PFKidsDepthInduct
import Tools.ShippingGen4FKidsLegacyFinal
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen5PFKidsDepthTop
namespace Tools.ShippingGen4FKidsObl
open Tools.ShippingGen4FKids Tools.ShippingGen4FKidsParams
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFrontA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4FKidsEntry
open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele
open Tools.ShippingGen4KWalkDepth
open Tools.Assume.FramedACases
open Tools.ShippingGen4FKidsDepth
open Tools.ShippingGen4FKidsEntryArms
open Tools.ShippingGen4FKidsDepthEntry
open Tools.ShippingGen4FKidsLegacyTail
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4FKidsDepthArms
open Tools.ShippingChildLegacyTailA
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingGen4FKidsTranslate
open Tools.ShippingGen4FKidsLegacyArm
open Tools.ShippingGen4FKidsFallback
open Tools.ShippingGen4FKidsLegacyCached
open Tools.ShippingGen4FKidsDepthInduct
open Tools.ShippingGen4FKidsLegacyFinal
open Tools.ShippingGen4FKidsDepthTop
open Tools.ShippingGen4ParamEntry

-- F-kids obligations (2) and (3) as SEPARATE theorems (the frozen fKids_memoHit / fKids_statePF / fKids are unchanged).
-- Premises: MemoFamily rev3 and MsgMvK, as in the frozen theorems. No new premise, no axiom, no sorry.
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- the parameter facts the `LegalBinding` assembly needs of the top module: no duplicate names, every name bound by θ -/
def ParamsOk (θ : List (String × Nat)) (m : Sparkle.IR.AST.Module) : Prop := PQ θ m.parameters

/-- (2)+(3) at the symbolic core: the returned top module declares distinct parameter names, each of them a name in θ. -/
theorem fKidsObl_params_core {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w') :
    (M0.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M0.parameters, p.name ∈ θ.map Prod.fst := by
  have hlog : LogMvKS O := logMvK_of M
  have hImpl : ∀ D, D ≠ 0 → ChildEntryKS O (WPF O D) → LegacyImplKS O (WPF O D) :=
    fun D _ hEntry => legacyImplKS_of_entry M hmsg (stableK_KWD O PPF D) hEntry
  have hD1 : (1 : Nat) ≠ 0 := Nat.one_ne_zero
  have hS := stableK_KWD O PPF 1
  have IH := synthesizeChild_depthPF M hlog hImpl 1 hD1
  have hsv : ∀ w, WPF O 1 w → sv w = some synthesizeChild := fun _ h => h.1.2.1
  have hEntry : ChildEntryKS O (WPF O 1) := by
    intro mctx' cctx' hA' c
    unfold childSynthEntry
    refine Triple.bindQ (tripleK_synthGetS M hA' hS hsv) ?_
    intro s hs
    subst hs
    dsimp only
    exact IH mctx' cctx' hA' c
  have htr : ∀ env : Lean.Environment, RecKS O (WPF O 1) (Tsyn env) := fun env => show RecKS O (WPF O 1) (fun e h t n => translateExprToWire env e h t n) from
    translate_keepsKS M hS env (hImpl 1 hD1 hEntry) (legacyCachedK_of_implS M hS (hImpl 1 hD1 hEntry)) hEntry
  have htop := entryTopSymP_windowD M hA (logMvK_of M) Tsyn declName θ
    (fun _ b env ci isInst => legacySymP_windowDP M hA hlog 1 (Tsyn env) b declName θ ci isInst (htr env))
  exact (runsTo_of_triple htop hw h).2

/-- (2)+(3) in the form of `fKids` (after `dropZeroWidthModule` / `mergeChecked`, which keep `parameters`). -/
theorem fKidsObl_params {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    (M'.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M'.parameters, p.name ∈ θ.map Prod.fst := by
  unfold synthesizeCombinationalWithParameters at h
  obtain ⟨⟨M0, D0⟩, w1, hcore, h⟩ := RunsTo.bind h
  have hP := fKidsObl_params_core M hmsg hA hw hcore
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, -⟩ := this
    subst h1
    simpa only [dropZero_pf] using hP
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, -⟩ := this
    subst h1
    simpa only [mergeChecked_pf, dropZero_pf] using hP

/-- Obligation (1), the part that IS provable: every module of the returned design declares no parameter, with NO name guard.
So a design module that collides with the top name (`x.name = M'.name`, which the walk cannot exclude, FKIDS_FREEZE §7.9) is a
parameter-free concrete module, never the symbolic top. The frozen `fKids` is this theorem restricted to `x.name ≠ M'.name`. -/
theorem fKidsObl_noGuard {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    ∀ x ∈ D'.modules, x.parameters = [] := by
  unfold synthesizeCombinationalWithParameters at h
  obtain ⟨⟨M0, D0⟩, w1, hcore, h⟩ := RunsTo.bind h
  have hD0 : DesignPF D0 := fKids_statePF M hmsg hA hw hcore
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  have hall : DesignPF D' := by
    rcases RunsTo.ite h with h | h
    · have := Tools.ShippingPostSoundness.RunsTo.pure h
      simp only [Prod.mk.injEq] at this
      obtain ⟨h1, h2⟩ := this
      subst h1 h2
      exact designPF_top _ (fun x hx => by unfold ParamFree at *; rw [dropZero_pf]; exact hx) M0 hD0
    · have := Tools.ShippingPostSoundness.RunsTo.pure h
      simp only [Prod.mk.injEq] at this
      obtain ⟨h1, h2⟩ := this
      subst h1 h2
      exact designPF_top _ (fun x hx => by unfold ParamFree at *; rw [mergeChecked_pf]; exact hx) M0
        (designPF_top _ (fun x hx => by unfold ParamFree at *; rw [dropZero_pf]; exact hx) M0 hD0)
  intro x hx
  exact hall x hx

end Tools.ShippingGen4FKidsObl

#print axioms Tools.ShippingGen4FKidsObl.fKidsObl_params_core
#print axioms Tools.ShippingGen4FKidsObl.fKidsObl_params
#print axioms Tools.ShippingGen4FKidsObl.fKidsObl_noGuard
