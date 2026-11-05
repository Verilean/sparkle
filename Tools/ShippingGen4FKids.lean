import Tools.ShippingGen4FKidsDepthInduct
import Tools.ShippingGen4FKidsLegacyFinal
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4FKidsDepthTop
-- F-kids, theorem (1) `fKids_memoHit` (FKIDS_FREEZE.md §2), statement as frozen.
-- Takes `MemoFamily` (rev3) and `MsgMvK` as HYPOTHESES `M`, `hmsg`; adds NO premise, NO axiom. No `sorry`.
-- (2) `fKids_statePF` and (3) `fKids` are NOT in this file yet (they need the symbolic top walk; FKIDS_FREEZE §7.7).
namespace Tools.ShippingGen4FKids
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

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (1) memo-hit / child-result part. A returning memoised child entry from a `WorldPF` world at depth `D ≠ 0` returns a
PairPF pair and gives a `WorldPF` world at the same depth. -/
theorem fKids_memoHit {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) (D : Nat) (hD : D ≠ 0) (c : Name) :
    Triple mctx mref cctx cref (WorldPF O D) (synthesizeChild c)
      (fun r w => WorldPF O D w ∧ PairPF r) (fun e w => WorldPF O D w ∧ OkExc e) := by
  have hlog : LogMvKS O := logMvK_of M
  have hImpl : ∀ D, D ≠ 0 → ChildEntryKS O (WPF O D) → LegacyImplKS O (WPF O D) :=
    fun D _ hEntry => legacyImplKS_of_entry M hmsg (stableK_KWD O PPF D) hEntry
  have h := synthesizeChild_depthPF M hlog hImpl D hD mctx cctx hA c
  have hfun : WorldPF O D = WPF O D := funext fun w => propext (worldPF_iff O D w)
  rw [hfun]
  exact h

theorem runsTo_of_triple {α : Type} {mctx : Meta.Context} {cctx : Core.Context} {P : Void IO.RealWorld → Prop}
    {m : MetaM α} {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : Triple mctx mref cctx cref P m Q R) {w w' : Void IO.RealWorld} {a : α} (hw : P w)
    (hr : RunsTo m mctx mref cctx cref w a w') : Q a w' := by
  have h1 := h w hw
  unfold RunsTo at hr
  rw [hr] at h1
  exact h1

/-- (2) the StatePF walk, as seen from the symbolic top. -/
theorem fKids_statePF {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w') :
    DesignPF D0 := by
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
  have htop := entryTopSym_windowD M hA (logMvK_of M) Tsyn declName θ
    (fun _ b env ci isInst => legacySym_windowDP M hA hlog 1 (Tsyn env) b declName θ ci isInst (htr env))
  exact runsTo_of_triple htop hw h

/-- (3) F-kids, in the form the `LegalBinding` assembly consumes (guard form of §1); in fact `DesignPF D'` is proved, the guard is not used. -/
theorem fKids {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = [] := by
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
  intro x hx _
  exact hall x hx

end Tools.ShippingGen4FKids

#print axioms Tools.ShippingGen4FKids.fKids_memoHit
#print axioms Tools.ShippingGen4FKids.fKids_statePF
#print axioms Tools.ShippingGen4FKids.fKids
