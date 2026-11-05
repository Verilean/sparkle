-- Gen5 port of Tools.ShippingGen4FKidsDepthInduct (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen5PFKidsLegacyArm
import Tools.ShippingGen4FKidsLegacyCached
import Tools.ShippingGen4FKidsFallback
-- F-kids DepthInduct: the depth induction, `PairPF` results, in the `WPF` world (the K walk's `child_step` / `child_budget`
-- with `LegacyImplKS` taken from the child entry, as in `LegacyInduct2`).
-- Takes `MemoFamily` and `MsgMvK` (through `LogMvKS`) as hypotheses only; adds NO premise, NO axiom. No `sorry`.
namespace Tools.ShippingGen4FKidsDepthInduct
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

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The depth-`D` statement for `synthesizeChild` in every admissible context: the result is `PairPF`. -/
def ChildAtPF (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ n,
    Triple mctx mref cctx cref (WPF O D) (synthesizeChild n)
      (fun r w => WPF O D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e)

section Induct
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hlog : LogMvKS O)
  (hImpl : ∀ D, D ≠ 0 → ChildEntryKS O (WPF O D) → LegacyImplKS O (WPF O D))
include M hlog hImpl

/-- **One level**: `synthesizeChild` at depth `D ≠ 0`, from `synthesizeChild` at depth `D + 1` (needed only below the limit). -/
theorem child_stepPF (D : Nat) (hD : D ≠ 0)
    (IH : D < sparkleSynthDepthLimit → ChildAtPF O (D + 1)) : ChildAtPF O D := by
  intro mctx cctx hA n
  have hD1 : D + 1 ≠ 0 := Nat.succ_ne_zero D
  have hS := stableK_KWD O PPF (D + 1)
  refine synthesizeChild_windowDP M hA D (fun n' => ?_) n
  refine combWith_nestedDP M hA hlog _ n' D hD (fun hlt b env ci isInst => ?_)
  have hchild : ∀ c, Triple mctx mref cctx cref (WPF O (D + 1)) (synthesizeChild c)
      (fun r w => WPF O (D + 1) w ∧ PairPF r) (fun e w => WPF O (D + 1) w ∧ OkExc e) :=
    fun c => IH hlt mctx cctx hA c
  have hsv : ∀ w, WPF O (D + 1) w → sv w = some synthesizeChild := fun _ h => h.1.2.1
  have hEntry : ChildEntryKS O (WPF O (D + 1)) := by
    intro mctx' cctx' hA' c
    unfold childSynthEntry
    refine Triple.bindQ (tripleK_synthGetS M hA' hS hsv) ?_
    intro s hs
    subst hs
    dsimp only
    exact IH hlt mctx' cctx' hA' c
  have htr := translate_keepsKS M hS env (hImpl (D + 1) hD1 hEntry)
    (legacyCachedK_of_implS M hS (hImpl (D + 1) hD1 hEntry)) hEntry
  exact fromConst_frontends_windowD M hA hlog (D + 1) (fun e h t n => translateExprToWire env e h t n) b n' ci
    isInst (htr mctx cctx hA) hchild
    (fun _ _ => legacy_windowDP M hA hlog (D + 1) _ b n' ci isInst htr)

/-- **The depth induction**: with the budget `k` (`sparkleSynthDepthLimit ≤ D + k`), `synthesizeChild` keeps `WPF O D` and returns `PairPF`. -/
theorem child_budgetPF : ∀ (k D : Nat), D ≠ 0 → sparkleSynthDepthLimit ≤ D + k → ChildAtPF O D := by
  intro k
  induction k with
  | zero =>
    intro D hD hk
    exact child_stepPF M hlog hImpl D hD (fun hlt => absurd hlt (by omega))
  | succ k ih =>
    intro D hD hk
    exact child_stepPF M hlog hImpl D hD
      (fun _ => ih (D + 1) (Nat.succ_ne_zero D) (by omega))

/-- **`synthesizeChild` at every nonzero depth**, result `PairPF`. -/
theorem synthesizeChild_depthPF (D : Nat) (hD : D ≠ 0) : ChildAtPF O D :=
  child_budgetPF M hlog hImpl sparkleSynthDepthLimit D hD (Nat.le_add_left _ _)

end Induct

end Tools.ShippingGen4FKidsDepthInduct

#print axioms Tools.ShippingGen4FKidsDepthInduct.synthesizeChild_depthPF
