import Tools.ShippingGen4KWalkInst
-- NOT BUILT (probe part built, rt167). S3 (part 3), telescope arm of scripts/gen4/KWALK_PLAN.md: `projFieldName?` for `StableK` (copy of ShippingChildProjFieldA).
-- `throwError` (MetaM) is shown to keep a `StableK` invariant by unfolding it into reads (`getEnv` = FramedNM.env, `getMCtx` = FramedNM.metaGet, `getRef`/`getLCtx`/`getOptions` = context reads)
-- plus the EXISTING `O.excOk` for the exception's message class; no `mv` law for `throwError` is needed. The telescope is `M.tele.telescope` (MemoFamily, approved).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkProjField
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

def throwPre (msg : MessageData) : MetaM (Syntax × MessageData) := do
  let ref ← getRef
  let x ← AddErrorMessageContext.add ref msg
  pure x

section T
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem keepsK_addMessageContext (msg : MessageData) :
    Keeps mctx mref cctx cref I (addMessageContext msg : MetaM MessageData) := by
  show Keeps mctx mref cctx cref I (Lean.addMessageContextFull msg)
  unfold Lean.addMessageContextFull
  refine Keeps.bind (keepsK_framedNM M hA hS FramedNM.env) fun env => ?_
  refine Keeps.bind (Keeps.bind (keepsK_framedNM M hA hS FramedNM.metaGet) fun _ => Keeps.pure _) fun mc => ?_
  refine Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) fun lc => ?_
  refine Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) fun op => ?_
  exact Keeps.pure _

theorem keepsK_throwError {α : Type} (msg : MessageData) (hmsg : OkMsg msg) :
    Keeps mctx mref cctx cref I (Lean.throwError msg : MetaM α) := by
  intro w hw
  have hq := hS.1 w hw
  have hpre : Keeps mctx mref cctx cref I
      (throwPre msg) := by
    unfold throwPre
    refine Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) fun ref => ?_
    refine Keeps.bind ?_ fun x => Keeps.pure _
    show Keeps mctx mref cctx cref I (do let m ← addMessageContext msg; pure (ref, m))
    exact Keeps.bind (keepsK_addMessageContext M hA hS msg) fun _ => Keeps.pure _
  have hk := hpre w hw
  have hexc := fun e w1 (hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w = .error e w1) =>
    O.excOk hA _ (Op.throwErr (α := α) msg hmsg) w e w1 hq hm
  unfold endW ErrOk
  cases hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w with
  | ok a w1 => exact (throwError_not_runs msg hm).elim
  | error e w1 =>
    have hm' : (match (throwPre msg) mctx mref cctx cref w with
        | .ok a s => EST.Out.error (Exception.error a.1 a.2) s
        | .error e s => EST.Out.error e s) = .error e w1 := hm
    unfold endW ErrOk at hk
    revert hk
    cases hp : (throwPre msg) mctx mref cctx cref w with
    | ok a w2 =>
      rw [hp] at hm'
      simp only [EST.Out.error.injEq] at hm'
      obtain ⟨-, rfl⟩ := hm'
      intro hk
      exact ⟨hk.1, hexc e w2 hm⟩
    | error e2 w2 =>
      rw [hp] at hm'
      simp only [EST.Out.error.injEq] at hm'
      obtain ⟨rfl, rfl⟩ := hm'
      intro hk
      exact ⟨hk.1, hexc e2 w2 hm⟩
theorem keepsK_getConstInfoInduct (n : Name) :
    Keeps mctx mref cctx cref I (getConstInfoInduct n : MetaM InductiveVal) := by
  unfold getConstInfoInduct isInductive?
  refine Keeps.bind (Keeps.bind (keepsK_framedNM M hA hS FramedNM.env) fun _ => Keeps.pure _) fun x => ?_
  cases x with
  | some a => exact Keeps.pure a
  | none => exact keepsK_throwError M hA hS _ (by okmsg)

theorem keepsK_getConstInfoCtor (n : Name) :
    Keeps mctx mref cctx cref I (getConstInfoCtor n : MetaM ConstructorVal) := by
  unfold getConstInfoCtor isCtor?
  refine Keeps.bind (Keeps.bind (keepsK_framedNM M hA hS FramedNM.env) fun env => ?_) fun x => ?_
  · split
    · split
      · exact Keeps.pure _
      · unfold panicWithPosWithDecl panic panicCore
        exact Keeps.pure _
    · exact Keeps.pure _
  · cases x with
    | some a => exact Keeps.pure a
    | none => exact keepsK_throwError M hA hS _ (by okmsg)

theorem keepsK_getUserName (id : FVarId) :
    Keeps mctx mref cctx cref I (id.getUserName : MetaM Name) := by
  unfold FVarId.getUserName FVarId.getDecl
  refine Keeps.bind (Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) fun l => ?_) fun d => Keeps.pure _
  cases l.find? id with
  | some d => exact Keeps.pure d
  | none => exact keepsK_framedNM M hA hS (FramedNM.fvarThrowUnknown id)

/-- **`projFieldName?` keeps a `StableK` invariant** (the telescope arm), from `MemoFamily` alone. -/
theorem projFieldNameK (n s : Name) :
    Keeps mctx mref cctx cref I (projFieldName? n s) := by
  unfold projFieldName?
  refine Keeps.bind (keepsK_framedNM M hA hS FramedNM.env) fun env => ?_
  split
  · rename_i projInfo _
    refine Keeps.bind (Keeps.tryCatch (Keeps.map _ (keepsK_getConstInfoInduct M hA hS s))
      fun e _ => Keeps.pure _) fun r => ?_
    split
    · rename_i indVal
      refine Keeps.bind (keepsK_getConstInfoCtor M hA hS _) fun ctorInfo => ?_
      refine Keeps.bind (M.tele.telescope I hA hS.1 hS.2 _ _
        (fun m c xs b hA' => ?_)) fun fieldName => Keeps.pure _
      refine Keeps.dite (fun h => ?_) (fun h => Keeps.pure _)
      exact Keeps.bind (keepsK_getUserName M hA' hS _) fun _ => Keeps.pure _
    · exact Keeps.pure _
  · exact Keeps.pure _

end T
end Tools.ShippingGen4KWalkProjField

#print axioms Tools.ShippingGen4KWalkProjField.keepsK_throwError
#print axioms Tools.ShippingGen4KWalkProjField.projFieldNameK
