import Tools.ShippingGen4KWalkDepthEntry
import Tools.ShippingGen4KWalkLegacyCached
-- NOT BUILT. S6 (depth induction, part 4) of scripts/gen4/KWALK_PLAN.md (frozen in scripts/gen4/KWALK_S6_FREEZE.md): THE DEPTH INDUCTION. `hchild := synthesizeChild_windowD`, `hbody := fromConst_frontends_windowD`,
-- `htr := translate_keepsK` are closed TOGETHER, by induction on the budget `k` with `sparkleSynthDepthLimit ≤ D + k` (measure `sparkleSynthDepthLimit - dv`): the entry throws at `D ≥ limit`, so the body is only walked below the limit.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. Remaining hypotheses (the only ones): `LogMvK` (Diag), `LegacyImplK` (which holds `PpMvK`'s consumers), `hleg` (the legacy arm).
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkDepthInduct
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

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **HYPOTHESIS `hleg`: the legacy arm** of `synthesizeFromConst` (both gates miss; the certified front end OFF), at a pinned depth, with the real translator:
from `KWD K D` to `KWD K_n D`, a failure leaves `KWD K D`. -/
def LegacyArmD (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (b : Bool) (env : Lean.Environment) (declName : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
      Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
        (synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (profLogIO b) declName [] false false ci isInst)
        (fun _ => KWD O (MemoKeysExc declName) D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e)

/-- The depth-`D` statement for `synthesizeChild`, in every admissible context. -/
def ChildAt (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ n,
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D) (synthesizeChild n)
      (fun _ => KWD O MemoKeysInChild D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e)

section Induct
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hlog : LogMvK O)
  (hImpl : ∀ D, D ≠ 0 → LegacyImplK O (KWD O MemoKeysInChild D))
  (hleg : ∀ D, D ≠ 0 → LegacyArmD O D)
include M hlog hImpl hleg

/-- **One level**: `synthesizeChild` at depth `D ≠ 0`, from `synthesizeChild` at depth `D + 1` (needed only below the limit). -/
theorem child_step (D : Nat) (hD : D ≠ 0)
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
  have htr := translate_keepsK M hS env (hImpl (D + 1) hD1)
    (legacyCachedK_of_impl M hS (hImpl (D + 1) hD1)) hEntry mctx cctx hA
  exact fromConst_frontends_windowD M hA hlog (D + 1) (fun e h t n => translateExprToWire env e h t n) b n' ci
    isInst htr hchild
    (fun hc hm => hleg (D + 1) hD1 mctx cctx hA b env n' ci isInst hc hm)

/-- **The depth induction**: with the budget `k` (`sparkleSynthDepthLimit ≤ D + k`, measure `limit - dv`), `synthesizeChild` keeps `KWD K D`. -/
theorem child_budget : ∀ (k D : Nat), D ≠ 0 → sparkleSynthDepthLimit ≤ D + k → ChildAt O D := by
  intro k
  induction k with
  | zero =>
    intro D hD hk
    exact child_step M hlog hImpl hleg D hD (fun hlt => absurd hlt (by omega))
  | succ k ih =>
    intro D hD hk
    exact child_step M hlog hImpl hleg D hD
      (fun _ => ih (D + 1) (Nat.succ_ne_zero D) (by omega))

/-- **`synthesizeChild` at every nonzero depth** (budget `sparkleSynthDepthLimit`): from `KWD K D` it returns in `KWD K D` (the depth is given back),
and fails in `KWD K D`. Hypotheses: `LogMvK`, `LegacyImplK`, `hleg` only. -/
theorem synthesizeChild_depthK (D : Nat) (hD : D ≠ 0) : ChildAt O D :=
  child_budget M hlog hImpl hleg sparkleSynthDepthLimit D hD (Nat.le_add_left _ _)

end Induct


/-! ## The connection to `memo_miss_of_child_miss` (MEMO_FAMILY_PROPOSAL §: K gives "child miss implies memo miss") -/

/-- **`memo_miss_of_child_miss`**, from K only: a name that is not a child-cache key is not a memo key. -/
theorem memo_miss_of_child_miss {m c : Std.HashMap Name Res} (h : MemoKeysInChild m c) {n : Name}
    (hc : c.contains n = false) : m.contains n = false := by
  cases hm : m.contains n with
  | false => rfl
  | true => rw [h n hm] at hc; exact absurd hc (by simp)

theorem contains_false_of_get?_none (c : Std.HashMap Name Res) {n : Name} (h : c.get? n = none) :
    c.contains n = false := by
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  simpa [Std.HashMap.get?_eq_getElem?] using h

/-- In a world satisfying `KWD K D`, a child-cache miss of `n` is a memo miss of `n`. -/
theorem memo_miss_of_child_miss_KWD {O : RefLawsAOps MkRefd mref cref} {D : Nat} {w : Void IO.RealWorld}
    (h : KWD O MemoKeysInChild D w) {n : Name} (hc : (cv w).contains n = false) : (mv w).contains n = false :=
  memo_miss_of_child_miss h.1.2.2 hc

section Miss
variable {mctx : Meta.Context} {cctx : Core.Context}
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The child-cache read in `synthesizeChild`: it returns the cache as it is, in `KWD K D` (it cannot throw). -/
theorem tripleK_cacheGetD (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (sparkleChildCache.get : MetaM (Std.HashMap Name Res))
      (fun c w => KWD O MemoKeysInChild D w ∧ c = cv w) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild D) FramedNM.cacheGet w hw
    have hf := O.frame hA _ FramedA.cacheGet w hw.1.1
    rw [endW_of_runs h] at hK hf
    exact ⟨hK.1, (runsTo_get_readOf _ h).trans hf.1.symm⟩

/-- **The connection**: the miss branch of `synthesizeChild` (the read says `n` is not cached) is a world where `n` is not in the memo either. -/
theorem childMiss_memoMiss (D : Nat) (n : Name) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (sparkleChildCache.get : MetaM (Std.HashMap Name Res))
      (fun c w => KWD O MemoKeysInChild D w ∧ (c.get? n = none → (mv w).contains n = false)) R :=
  Triple.conseq (tripleK_cacheGetD M hA D) (fun _ h => h)
    (fun c w h => ⟨h.1, fun hn => by
      obtain ⟨hw, hc⟩ := h
      subst hc
      exact memo_miss_of_child_miss_KWD hw (contains_false_of_get?_none _ hn)⟩)
    (fun _ _ h => h)

end Miss

end Tools.ShippingGen4KWalkDepthInduct

#print axioms Tools.ShippingGen4KWalkDepthInduct.child_step
#print axioms Tools.ShippingGen4KWalkDepthInduct.child_budget
#print axioms Tools.ShippingGen4KWalkDepthInduct.synthesizeChild_depthK
#print axioms Tools.ShippingGen4KWalkDepthInduct.childMiss_memoMiss
