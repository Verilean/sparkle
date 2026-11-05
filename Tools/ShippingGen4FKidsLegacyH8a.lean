import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH7
import Tools.ShippingGen4FKidsLegacyH7
import Tools.ShippingGen4KWalkLegacyRules
import Tools.ShippingGen4FKidsLegacyRules
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH8a exit 0 (rt175, source as of this commit); clean build is the coder's. LegacyImplKS part 8a: the two diagnostic rules `handleDefinitionUnfold` needs:
-- the stderr pair (Elab.lean 6423-6425) as ONE `KeepsCS` unit (`stderrLine`), and `msgToString` of a message in the class (Elab.lean 6605; the memo law is the HYPOTHESIS `MsgMvK`).
-- Takes `MemoFamily` (TRUSTED, approved) and `MsgMvK` as HYPOTHESES; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH8a
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
open Tools.ShippingGen4KWalkTac2
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4FKidsEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4FKidsLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4FKidsLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4FKidsCanon
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4FKidsDiag

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

theorem metaM_bind_assocS {α β γ : Type} (x : MetaM α) (f : α → MetaM β) (g : β → MetaM γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  funext mctx mref cctx cref w
  change EST.bind (EST.bind (x mctx mref cctx cref) (fun a => f a mctx mref cctx cref)) (fun b => g b mctx mref cctx cref) w =
    EST.bind (x mctx mref cctx cref) (fun a => EST.bind (f a mctx mref cctx cref) (fun b => g b mctx mref cctx cref)) w
  unfold EST.bind
  cases hx : x mctx mref cctx cref w with
  | ok a w1 =>
    cases hf : f a mctx mref cctx cref w1 with
    | ok b w2 => simp [hx, hf]
    | error e w2 => simp [hx, hf]
  | error e w1 => simp [hx]

/-- Two `liftMetaM` binds are one `liftMetaM` of the bind (a rewrite of the `CompilerM` plumbing only). -/
theorem liftMetaM_bind_unitS (a b : MetaM Unit) :
    ((CompilerM.liftMetaM a : CompilerM Unit) >>= fun _ => CompilerM.liftMetaM b) = CompilerM.liftMetaM (a >>= fun _ => b) := by
  funext ctx st
  unfold CompilerM.liftMetaM
  simp only [liftM, monadLift, MonadLift.monadLift]
  show (((a >>= fun x => pure (x, st) : MetaM _) >>= fun p => (b >>= fun y => pure (y, p.2) : MetaM _)) : MetaM _) =
    ((a >>= fun _ => b) >>= fun y => pure (y, st) : MetaM _)
  rw [metaM_bind_assocS, metaM_bind_assocS]
  congr 1

theorem metaM_pure_bindS {α β : Type} (a : α) (f : α → MetaM β) : (pure a >>= f : MetaM β) = f a := by
  funext mctx mref cctx cref w
  rfl

/-- The same with a continuation after the second lift. -/
theorem liftMetaM_bind_kS {β : Type} (a b : MetaM Unit) (k : Unit → CompilerM β) :
    ((CompilerM.liftMetaM a : CompilerM Unit) >>= fun _ => (CompilerM.liftMetaM b : CompilerM Unit) >>= k) =
      ((CompilerM.liftMetaM (a >>= fun _ => b) : CompilerM Unit) >>= k) := by
  funext ctx st
  unfold CompilerM.liftMetaM
  simp only [liftM, monadLift, MonadLift.monadLift]
  show (((a >>= fun x => pure (x, st) : MetaM _) >>= fun p =>
      (((b >>= fun y => pure (y, p.2) : MetaM _)) >>= fun q => k q.1 ctx q.2 : MetaM _)) : MetaM _) =
    ((((a >>= fun _ => b) >>= fun y => pure (y, st) : MetaM _)) >>= fun p => k p.1 ctx p.2 : MetaM _)
  simp only [metaM_bind_assocS, metaM_pure_bindS]

theorem bind_run_okS {α β : Type} (x : MetaM α) (f : α → MetaM β) (w w1 : Void IO.RealWorld) (a : α)
    (h : x mctx mref cctx cref w = .ok a w1) : (x >>= f) mctx mref cctx cref w = f a mctx mref cctx cref w1 := by
  change EST.bind (x mctx mref cctx cref) (fun a => f a mctx mref cctx cref) w = _
  unfold EST.bind; rw [h]

theorem bind_run_errS {α β : Type} (x : MetaM α) (f : α → MetaM β) (w w1 : Void IO.RealWorld) (e : Exception)
    (h : x mctx mref cctx cref w = .error e w1) : (x >>= f) mctx mref cctx cref w = .error e w1 := by
  change EST.bind (x mctx mref cctx cref) (fun a => f a mctx mref cctx cref) w = _
  unfold EST.bind; rw [h]

section H8a
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
include M hS hA

/-- **The stderr pair** (Elab.lean 6423-6425): `eprintln` then `flushStderr` keeps the invariant (the memo by `stderrLine`). -/
theorem keepsK_stderrPairS (s : String) :
    Keeps mctx mref cctx cref I ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) := by
  intro w hw
  have hq := hS.1 w hw
  have hm := M.stderrLine hA s w hq
  have ha := O.diag hA (liftM (IO.eprintln s) : MetaM Unit) (Diag.ioEprintln s) w hq
  cases hx : (liftM (IO.eprintln s) : MetaM Unit) mctx mref cctx cref w with
  | ok x w1 =>
    have eA : endW mctx mref cctx cref (liftM (IO.eprintln s) : MetaM Unit) w = w1 := by
      unfold endW; rw [hx]
    rw [eA] at ha
    have hb := O.diag hA (liftM Sparkle.Compiler.flushStderr : MetaM Unit) Diag.stderrFlush w1 ha.2
    have hrun := bind_run_okS (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      (liftM (IO.eprintln s) : MetaM Unit) (fun _ => (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w w1 x hx
    have eP : endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
        (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w =
        endW mctx mref cctx cref (liftM Sparkle.Compiler.flushStderr : MetaM Unit) w1 := by
      unfold endW; rw [hrun]
    rw [eP] at hm
    refine ⟨?_, ?_⟩
    · rw [eP]
      exact hS.2 w _ (hb.1.1.trans ha.1.1) (hb.1.2.1.trans ha.1.2.1) (hb.1.2.2.trans ha.1.2.2) hm (fun _ => hb.2) hw
    · unfold ErrOk; rw [hrun]
      cases hy : (liftM Sparkle.Compiler.flushStderr : MetaM Unit) mctx mref cctx cref w1 with
      | ok a w2 => exact True.intro
      | error e w2 => exact O.excOk hA _ (.diag Diag.stderrFlush) w1 e w2 ha.2 hy
  | error e w1 =>
    have eA : endW mctx mref cctx cref (liftM (IO.eprintln s) : MetaM Unit) w = w1 := by
      unfold endW; rw [hx]
    rw [eA] at ha
    have hrun := bind_run_errS (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      (liftM (IO.eprintln s) : MetaM Unit) (fun _ => (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w w1 e hx
    have eP : endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
        (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w = w1 := by
      unfold endW; rw [hrun]
    rw [eP] at hm
    refine ⟨?_, ?_⟩
    · rw [eP]
      exact hS.2 w _ ha.1.1 ha.1.2.1 ha.1.2.2 hm (fun _ => ha.2) hw
    · unfold ErrOk; rw [hrun]
      exact O.excOk hA _ (.diag (Diag.ioEprintln s)) w e w1 hq hx

end H8a

section H8b
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O)
include M hS hmsg

/-- `msgToString` of a message in the class (Elab.lean 6605). -/
theorem keepsK_msgToStringRS (hA : AdmCtx O.quiet mctx cctx) (m : MessageData) (hm : OkMsg m) :
    Keeps mctx mref cctx cref I (liftM m.toString : MetaM String) := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.diag hA _ (Diag.msgToString m hm) w hq
  have hmv := hmsg mctx cctx hA m hm w hq
  refine ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 hmv (fun _ => hk.2) hw, ?_⟩
  unfold ErrOk
  cases hmm : (liftM m.toString : MetaM String) mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e' w1 => exact O.excOk hA _ (.diag (Diag.msgToString m hm)) w e' w1 hq hmm

end H8b

section H8c
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
include M hS hA

/-- The stderr pair as ONE `CompilerM` unit, followed by the rest of the program. -/
theorem stderrPairCPkS {β : Type} (s : String) (k : Unit → CompilerM β)
    (hk : ∀ u, KeepsCS mctx mref cctx cref I (k u)) :
    KeepsCS mctx mref cctx cref I ((CompilerM.liftMetaM (liftM (IO.eprintln s) : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM Sparkle.Compiler.flushStderr : MetaM Unit) : CompilerM Unit) >>= k) := by
  rw [liftMetaM_bind_kS]
  exact KeepsCS.bind (KeepsCS.lift (keepsK_stderrPairS M hS hA s)) hk

end H8c

set_option hygiene false in
macro "kwAll2" : tactic => `(tactic| swalkN [stderrPairCPkS M hS hA _ _, keepsK_msgToStringRS M hS hmsg hA _ _, keepsK_addMessageContextS M hA hS _, keepsK_ppExprS M hpp hS _ _,
  keepsK_throwErrorS M _ hS _ _, keepsK_getDeclS M hpp hS _ _, Keeps.withReaderA (q := O.quiet) _ _,
  extractWidthKS M hpp hS _ _, inferHWTypeKS M hpp hS _ _, extractDimExprKS M hpp hS _ _,
  inferHWTypeWithDimensionsKS M hpp hS _ _, inferHWTypeFromSignalKS M hpp hS _ _,
  isSignalBinderTypeKS M hpp hS _ _, extractNatKS M hpp hS _ _, getWireWidthKS M hpp hS _ _,
  getWireWidthDimKS M hpp hS _ _, cachedInferTypeKS M hpp hS _ _, extractBitVecLiteralKS M hpp hS _ _,
  extractNatLiteralKS M hpp hS _ _, extractBitVecListKS M hpp hS _ _, extractBitVecArrayKS M hpp hS _ _,
  lowerZeroExtendWireKS M hpp hS _ _ _ _ _,
  isTracingEnabledFor_keepsKS M hpp hS _ _, addTrace_keepsKS M hpp hS _ _ _,
  snapshotWireCaches_keepsKS M hpp hS _, restoreWireCaches_keepsKS M hpp hS _ _,
  makeWirePS M hA hS, addInputPS M hA hS, addOutputPS M hA hS, emitAssignP, bindSourceVariableP, lookupVarP,
  emitRegisterStmtA, emitRegisterK M hA hS, emitMemoryK M hA hS, freshNameA, emitInstanceA,
  canonHardwareKeyKS M hA hS _, withLocalDeclPKS M hS hA _ _ _, withLetDeclPKS M hS hA _ _ _ _, M.tele.telescope I _ hS.1 hS.2 _ _,
  addModuleToDesignA, withVarMappingP, withDimVarMappingPS, KeepsCS.tryCatch, KeepsCS.map _,
  keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))])


end Tools.ShippingGen4FKidsLegacyH8a
