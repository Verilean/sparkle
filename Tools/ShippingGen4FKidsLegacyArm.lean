import Tools.ShippingGen4FKidsDepthEntry
import Tools.ShippingGen4FKidsLegacyTail
import Tools.ShippingGen4KWalkDiag
import Tools.ShippingGen4KWalkEntryCore
-- F-kids LegacyArm: `legacy_windowD` of the K walk, PairPF result, state-tracked bind walk (`bindInputsLegacyKPS`, parameters = []).
-- Takes MemoFamily and MsgMvK as hypotheses only; no sorry.
namespace Tools.ShippingGen4FKidsLegacyArm
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Arm
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

omit M hA in
/-- `WPF O D` weakens to `WPFX O n D` (a step that leaves the world as it is). -/
theorem wpfX_of_wpf {O : RefLawsAOps MkRefd mref cref} {D : Nat} {n : Name} {w : Void IO.RealWorld}
    (h : WPF O D w) : WPFX O n D w :=
  ⟨⟨h.1.1, h.1.2.1, ⟨memoKeysInChild_exc n h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩⟩, h.2⟩

/-- The memo read under the PF world: returns the memo, whose entries are `PairPF`. -/
theorem tripleK_memoGetDP (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (WPF O D)
      (sparkleSubModuleCache.get : MetaM (Std.HashMap Name Res))
      (fun m w => WPF O D w ∧ CachePF m) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keeps_KW_memoGet M hA PPF w hw.1
    have hp : FramedA MkRefd (sparkleSubModuleCache.get : MetaM (Std.HashMap Name Res)) :=
      framedA_of_memoAccess MemoAccess.get
    have hf := O.frame hA _ hp w hw.1.1
    rw [endW_of_runs h] at hK hf
    have ha : a = mv w := runsTo_get_readOf _ h
    exact ⟨⟨hK.1, by rw [hf.2.2]; exact hw.2⟩, by rw [ha]; exact hw.1.2.2.2.1⟩

theorem legacy_windowDP (hlog : LogMvKS O) (D : Nat)
    (translate : TranslateFn) (b : Bool) (declName : Name) (constInfo : ConstantInfo)
    (isInst : Lean.Expr → Bool)
    (htr : RecKS O (WPF O D) translate) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeFromConst translate (profLogIO b) declName [] false false constInfo isInst)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
  have hS := stableK_KWD O PPF D
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true, List.isEmpty_nil]
  refine triple_pure_bind_ofS ?_
  dsimp only
  refine triple_pure_bind_ofS ?_
  dsimp only
  refine Triple.bindQ (P' := WPF O D) (φ := CachePF) (tripleK_memoGetDP M hA D) ?_
  intro memo hmemo
  cases hg : memo.get? declName with
  | some cached =>
    dsimp only
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
    intro _
    exact Triple.pure fun w hw => ⟨wpfX_of_wpf hw,
      hmemo declName cached hg⟩
  | none =>
    dsimp only
    refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
    intro _
    cases constInfo with
    | defnInfo di =>
      dsimp only
      have hpp : PpMvKS O := ppMvK_of M
      refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
      intro _
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.monoMs)) ?_
      intro t0
      refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
      intro _
      refine Triple.bind (keeps_iff.mp (openRecordInputs_keepsKS M hS hA _)) ?_
      intro body0
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.monoMs)) ?_
      intro t1
      refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA hS hlog b _)) ?_
      intro _
      refine M.tele.lamTelescopeT (WPF O D) (fun r w => WPFX O declName D w ∧ PairPF r)
        (WPF O D) hA (fun _ h => h.1.1) (fun _ _ h => h.1.1.1) (fun _ h => h.1.1)
        (stableK_KWD O PPF D).2
        (fun _ w w' h1 h2 h3 h4 hq hw => ⟨(stableK_KWD O (PPFX declName) D).2 w w' h1 h2 h3 h4 hq hw.1, hw.2⟩)
        (stableK_KWD O PPF D).2 _ _ _ ?_
      intro mctx' cctx' xs innerBody hA'
      refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA' hS hlog b _)) ?_
      intro _
      refine Triple.bind (keeps_iff.mp (splitReturnLeaves_keepsKS M hS hA' _ _)) ?_
      intro leaves
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA' hS FramedNM.monoMs)) ?_
      intro t2
      refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA' hS hlog b _)) ?_
      intro _
      refine Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCacheS M hA' hS _) ?_
      intro cacheRef hr
      have hi := init_ok (Sparkle.IR.ModuleName.ofDecl declName)
      refine Triple.bindQ (P' := WPF O D)
        (φ := fun p => GoodS (Sparkle.IR.Builder.CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) p.2)
        ?hh ?_
      case hh =>
        exact (bindInputsLegacyKPS M hpp hS hA' [] rfl false xs _
          (emitLeavesKPS M hA' hS hlog translate b cacheRef hr (htr mctx' cctx' hA') _ _ _) 0) _ _
          (ctxOk_entry false hr) hi.1
      rintro ⟨_, fs⟩ hg
      refine Triple.bindQ (P' := WPF O D) (φ := PairPF)
        (finishSynthPS declName fs hg.2.1 (hg.2.2.mp hi.2)) ?_
      intro result hres
      refine Triple.bind (triple_memoInsertDP M hA' D declName result hres) ?_
      intro _
      exact Triple.pure fun _ hw => ⟨hw, hres⟩
    | _ =>
      dsimp only
      exact tripleK_throwErr M hA hS _ (by okmsg)

end Arm
end Tools.ShippingGen4FKidsLegacyArm

#print axioms Tools.ShippingGen4FKidsLegacyArm.legacy_windowDP
