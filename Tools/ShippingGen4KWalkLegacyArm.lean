import Tools.ShippingGen4KWalkDepthInduct
import Tools.ShippingGen4KWalkLegacyTail
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4KWalkEntryCore
import Tools.ShippingGen4KWalkTranslate
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyArm exit 0 (part of the 768-job Tests.Gen4.KWalkLegacyCheck build) (rt173, source as of 8f112bcc). Clean build is the coder's.: stage 2, the legacy arm (Elab.lean 5340-5389) for `KWD`.
namespace Tools.ShippingGen4KWalkLegacyArm
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildLegacyTailA
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryArms
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4KWalkLegacyTail
open Tools.ShippingGen4KWalkDepth
open Tools.ShippingGen4KWalkDepthArms
open Tools.ShippingGen4KWalkDepthInduct
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4KWalkTranslate
open Tools.Assume.FramedACases

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Arm
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

omit M hA in
/-- `KWD K D` weakens to `KWD K_n D` (a step that leaves the world as it is). -/
theorem kwdX_of_kwd {O : RefLawsAOps MkRefd mref cref} {D : Nat} {n : Name} {w : Void IO.RealWorld}
    (h : KWD O MemoKeysInChild D w) : KWD O (MemoKeysExc n) D w :=
  ⟨⟨h.1.1, h.1.2.1, memoKeysInChild_exc n h.1.2.2⟩, h.2⟩

/-- The memo read: returns the memo as it is, in `KWD K D` (it cannot throw). -/
theorem tripleK_memoGetD (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (sparkleSubModuleCache.get : MetaM (Std.HashMap Name Res))
      (fun _ w => KWD O MemoKeysInChild D w) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keeps_KW_memoGet M hA MemoKeysInChild w hw.1
    have hp : FramedA MkRefd (sparkleSubModuleCache.get : MetaM (Std.HashMap Name Res)) :=
      framedA_of_memoAccess MemoAccess.get
    have hf := O.frame hA _ hp w hw.1.1
    rw [endW_of_runs h] at hK hf
    exact ⟨hK.1, by rw [hf.2.2]; exact hw.2⟩

theorem legacy_windowD (hlog : LogMvK O) (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (htr : RecK O (KWD O MemoKeysInChild D) translate) :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)
      (fun _ => KWD O (MemoKeysExc declName) D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e) := by
  have hS := stableK_KWD O MemoKeysInChild D
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true, List.isEmpty_nil]
  refine triple_pure_bind_of ?_
  dsimp only
  refine triple_pure_bind_of ?_
  dsimp only
  refine Triple.bind (tripleK_memoGetD M hA D) (fun memo => ?_)
  cases hg : memo.get? declName with
  | some cached =>
    dsimp only
    refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA hS hlog b _)) ?_
    intro _
    exact Triple.pure fun _ hw => kwdX_of_kwd hw
  | none =>
    dsimp only
    refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA hS hlog b _)) ?_
    intro _
    cases constInfo with
    | defnInfo di =>
      dsimp only
      have hpp : PpMvK O := ppMvK_of M
      refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA hS hlog b _)) ?_
      intro _
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.monoMs)) ?_
      intro t0
      refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA hS hlog b _)) ?_
      intro _
      refine Triple.bind (keeps_iff.mp (openRecordInputs_keepsK M hS hA _)) ?_
      intro body0
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.monoMs)) ?_
      intro t1
      refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA hS hlog b _)) ?_
      intro _
      refine M.tele.lamTelescopeT (KWD O MemoKeysInChild D) (fun _ => KWD O (MemoKeysExc declName) D)
        (KWD O MemoKeysInChild D) hA (fun _ h => h.1.1) (fun _ _ h => h.1.1) (fun _ h => h.1.1)
        (stableK_KWD O MemoKeysInChild D).2 (fun _ => (stableK_KWD O (MemoKeysExc declName) D).2)
        (stableK_KWD O MemoKeysInChild D).2 _ _ _ ?_
      intro mctx' cctx' xs innerBody hA'
      refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA' hS hlog b _)) ?_
      intro _
      refine Triple.bind (keeps_iff.mp (splitReturnLeaves_keepsK M hS hA' _ _)) ?_
      intro leaves
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA' hS FramedNM.monoMs)) ?_
      intro t2
      refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA' hS hlog b _)) ?_
      intro _
      refine Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCache M hA' hS _) ?_
      intro cacheRef hr
      refine Triple.bind (keeps_iff.mp ((bindInputsLegacyKP M hpp hS hA' [] false xs _
        (emitLeavesKP M hA' hS hlog translate b cacheRef hr (htr mctx' cctx' hA') _ _ _) 0) _ _
        (ctxOk_entry false hr))) ?_
      rintro ⟨_, fs⟩
      refine Triple.bind (finishSynthA declName fs) ?_
      intro result
      refine Triple.bind (triple_memoInsertD M hA' D declName result) ?_
      intro _
      exact Triple.pure fun _ hw => hw
    | _ =>
      dsimp only
      exact tripleK_throwErr M hA hS _ (by okmsg)

end Arm
end Tools.ShippingGen4KWalkLegacyArm
