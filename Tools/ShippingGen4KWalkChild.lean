import Tools.ShippingGen4KWalkEntryCore
import Tools.ShippingGen4KWalkEnv
-- BUILT: kjob lake build Tools.ShippingGen4KWalkChild exit 0 (rt169, source as of 9e5eb088); axioms standard only. Clean build is the coder's. S6 (first part) of scripts/gen4/KWALK_PLAN.md: `synthesizeCombinationalWith` and `synthesizeChild` for `KWalk`. The window is CLOSED here: `synthesizeChild` runs the entry (K to K_n), then inserts into the child cache (K_n to K).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. DIAG-PENDING hypothesis `LogMvK` (see Entry). No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkChild
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
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryCore

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Child
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- `synthesizeCombinationalWith` for a NESTED run: the entry (K to K_declName), the `IO.getEnv`, the pure
post-processing. The post-processing is inside the window and cannot throw (`ioEnv_runs`). -/
theorem combWith_nestedK (hlog : LogMvK O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (hbody : ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KWalk O)
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e)) :
    Triple mctx mref cctx cref (fun w => KWalk O w ∧ dv w ≠ 0)
      (synthesizeCombinationalWith translate declName)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
  unfold synthesizeCombinationalWith
  refine Triple.bind (entryNested_windowK M hA hlog translate declName hbody) ?_
  rintro ⟨m, d⟩
  dsimp only
  refine Triple.bind (triple_framedNM_total M hA (MemoKeysExc declName) (FramedNM.ioEnv _)
    (fun w => Tools.ShippingGen4KWalkEnv.ioEnv_runs _ w)) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- **`synthesizeChild`: the window is closed.** Given the entry for a nested run (`hcomb`: K to K_n, K on failure),
the memoised child entry returns in K and fails in K. -/
theorem synthesizeChild_windowK
    (hcomb : ∀ n, Triple mctx mref cctx cref (fun w => KWalk O w ∧ dv w ≠ 0) (synthesizeCombinational n)
      (fun _ => KWalkX O n) (fun e w => KWalk O w ∧ OkExc e)) (n : Name) :
    Triple mctx mref cctx cref (fun w => KWalk O w ∧ dv w ≠ 0) (synthesizeChild n)
      (fun _ => KWalk O) (fun e w => KWalk O w ∧ OkExc e) := by
  unfold synthesizeChild
  refine Triple.bind (R := fun e w => KWalk O w ∧ OkExc e) (Q := fun _ w => KWalk O w ∧ dv w ≠ 0)
    (Triple.conseq (keeps_iff.mp (keepsK_framedNM M hA (stableK_KD (O := O)) FramedNM.cacheGet))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro cache
  split
  · exact Triple.pure fun w hw => hw.1
  · refine Triple.bind (hcomb n) ?_
    intro r
    refine Triple.bind (Triple.of_runs (refModify_runs _ _) fun w u w' hw h =>
      kwalk_childInsert M hA n r h hw) ?_
    intro _
    exact Triple.pure fun w hw => hw

end Child

end Tools.ShippingGen4KWalkChild

#print axioms Tools.ShippingGen4KWalkChild.combWith_nestedK
#print axioms Tools.ShippingGen4KWalkChild.synthesizeChild_windowK
