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

end Tools.ShippingGen4KWalkDepthInduct

#print axioms Tools.ShippingGen4KWalkDepthInduct.child_step
#print axioms Tools.ShippingGen4KWalkDepthInduct.child_budget
#print axioms Tools.ShippingGen4KWalkDepthInduct.synthesizeChild_depthK
