import Tools.ShippingGen4KWalkLegacyInduct
-- NOT BUILT (rt175 WIP). The depth induction of `Induct` with the main-body hypothesis in the form `hImpl : ∀ D ≠ 0, ChildEntryK (KWD D) → LegacyImplK (KWD D)`: `hEntry` (built from `IH` by `tripleK_synthGet`) is handed to `hImpl`, so `ChildEntryK` is not a hypothesis.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyInduct2
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4KWalkFallback
open Tools.ShippingGen4KWalkLegacyCached
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkDepth
open Tools.ShippingGen4KWalkDepthArms
open Tools.ShippingGen4KWalkDepthEntry
open Tools.ShippingGen4KWalkDepthInduct
open Tools.ShippingGen4KWalkDepthTop
open Tools.ShippingGen4KWalkLegacyArm
open Tools.ShippingGen4KWalkDiag

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Induct
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hlog : LogMvK O)
  (hImpl : ∀ D, D ≠ 0 → ChildEntryK O (KWD O MemoKeysInChild D) → LegacyImplK O (KWD O MemoKeysInChild D))
include M hlog hImpl

theorem child_stepL2 (D : Nat) (hD : D ≠ 0)
    (IH : D < sparkleSynthDepthLimit → ChildAt O (D + 1)) : ChildAt O D := by
  intro mctx cctx hA n
  have hD1 : D + 1 ≠ 0 := Nat.succ_ne_zero D
  have hS := stableK_KWD O MemoKeysInChild (D + 1)
  refine synthesizeChild_windowD M hA D (fun n' => ?_) n
  refine combWith_nestedD M hA hlog _ n' D hD (fun hlt b env ci isInst => ?_)
  have hchild : ∀ c, Keeps mctx mref cctx cref (KWD O MemoKeysInChild (D + 1)) (synthesizeChild c) :=
    fun c => keeps_iff.mpr (IH hlt mctx cctx hA c)
  have hsv : ∀ w, KWD O MemoKeysInChild (D + 1) w → sv w = some synthesizeChild := fun _ h => h.1.2.1
  have hEntry : ChildEntryK O (KWD O MemoKeysInChild (D + 1)) := by
    intro mctx' cctx' hA' c
    have hchild' : ∀ c, Keeps mctx' mref cctx' cref (KWD O MemoKeysInChild (D + 1)) (synthesizeChild c) :=
      fun c => keeps_iff.mpr (IH hlt mctx' cctx' hA' c)
    refine keeps_iff.mpr ?_
    unfold childSynthEntry
    refine Triple.bindQ (tripleK_synthGet M hA' hS hsv) ?_
    intro s hs
    subst hs
    dsimp only
    exact keeps_iff.mp (hchild' c)
  have htr := translate_keepsK M hS env (hImpl (D + 1) hD1 hEntry)
    (legacyCachedK_of_impl M hS (hImpl (D + 1) hD1 hEntry)) hEntry
  exact fromConst_frontends_windowD M hA hlog (D + 1) (fun e h t n => translateExprToWire env e h t n) b n' ci
    isInst (htr mctx cctx hA) hchild
    (fun _ _ => legacy_windowD M hA hlog (D + 1) _ b n' ci isInst htr)

theorem child_budgetL2 : ∀ (k D : Nat), D ≠ 0 → sparkleSynthDepthLimit ≤ D + k → ChildAt O D := by
  intro k
  induction k with
  | zero =>
    intro D hD hk
    exact child_stepL2 M hlog hImpl D hD (fun hlt => absurd hlt (by omega))
  | succ k ih =>
    intro D hD hk
    exact child_stepL2 M hlog hImpl D hD
      (fun _ => ih (D + 1) (Nat.succ_ne_zero D) (by omega))

/-- **`synthesizeChild` at every nonzero depth**, without `hleg`. Hypotheses: `LogMvK`, `LegacyImplK`. -/
theorem synthesizeChild_depthKL2 (D : Nat) (hD : D ≠ 0) : ChildAt O D :=
  child_budgetL2 M hlog hImpl sparkleSynthDepthLimit D hD (Nat.le_add_left _ _)

variable (hA : AdmCtx O.quiet mctx cctx)
include hA

/-- **The outermost entry of the K walk, without `hleg`**. Hypotheses: `LogMvK`, `LegacyImplK`. -/
theorem topEntry_KL2 (declName : Name) :
    Triple mctx mref cctx cref (KWD O (fun _ _ => True) 0)
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)
      (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
  refine entryTop_windowD M hA hlog _ declName (fun _ b env ci isInst => ?_)
  have hD1 : (1 : Nat) ≠ 0 := Nat.one_ne_zero
  have hS := stableK_KWD O MemoKeysInChild 1
  have IH := synthesizeChild_depthKL2 M hlog hImpl 1 hD1
  have hchild : ∀ c, Keeps mctx mref cctx cref (KWD O MemoKeysInChild 1) (synthesizeChild c) :=
    fun c => keeps_iff.mpr (IH mctx cctx hA c)
  have hsv : ∀ w, KWD O MemoKeysInChild 1 w → sv w = some synthesizeChild := fun _ h => h.1.2.1
  have hEntry : ChildEntryK O (KWD O MemoKeysInChild 1) := by
    intro mctx' cctx' hA' c
    have hchild' : ∀ c, Keeps mctx' mref cctx' cref (KWD O MemoKeysInChild 1) (synthesizeChild c) :=
      fun c => keeps_iff.mpr (IH mctx' cctx' hA' c)
    refine keeps_iff.mpr ?_
    unfold childSynthEntry
    refine Triple.bindQ (tripleK_synthGet M hA' hS hsv) ?_
    intro s hs
    subst hs
    dsimp only
    exact keeps_iff.mp (hchild' c)
  have htr := translate_keepsK M hS env (hImpl 1 hD1 hEntry) (legacyCachedK_of_impl M hS (hImpl 1 hD1 hEntry)) hEntry
  exact Tools.ShippingGen4KWalkDepthArms.fromConst_frontends_windowD M hA hlog 1
    (fun e h t n => translateExprToWire env e h t n) b declName ci isInst (htr mctx cctx hA) hchild
    (fun _ _ => legacy_windowD M hA hlog 1 _ b declName ci isInst htr)

omit hlog in
/-- The same, with `LogMvK` derived from the family (`logProf`): the only hypothesis left is `LegacyImplK`. -/
theorem topEntry_K_of_family2 (declName : Name) :
    Triple mctx mref cctx cref (KWD O (fun _ _ => True) 0)
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)
      (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) :=
  topEntry_KL2 M (logMvK_of M) hImpl hA declName

end Induct

end Tools.ShippingGen4KWalkLegacyInduct2

#print axioms Tools.ShippingGen4KWalkLegacyInduct2.synthesizeChild_depthKL2
#print axioms Tools.ShippingGen4KWalkLegacyInduct2.topEntry_KL2
#print axioms Tools.ShippingGen4KWalkLegacyInduct2.topEntry_K_of_family2
