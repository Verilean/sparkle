import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen4KWalkEntryArms
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
-- BUILT: kjob lake build Tools.ShippingGen4KWalkDiag exit 0 (part of the 756-job Tests.Gen4.MemoFamilyCheck build) (rt173, source as of 155e13c4). Clean build is the coder's.
--   `LogMvK` is the field `logProf`; `PpMvK` follows from `printersMv` + the existing `frame` (`ppExpr_mv`).
-- `MsgMvK` (Elab.lean 6605) is NOT a family statement: it stays a hypothesis `def`. No new law / TRUSTED statement. No sorry, no axiom, no native_decide.

open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildBndCore Tools.Assume.MemoFamily
open Sparkle.Compiler.Elab

namespace Tools.ShippingGen4KWalkDiag

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable {O : RefLawsAOps MkRefd mref cref}

theorem liftIOCore_bind {α β : Type} (x : IO α) (f : α → IO β) :
    (Core.liftIOCore (x >>= f) : CoreM β) = (Core.liftIOCore x >>= fun a => Core.liftIOCore (f a) : CoreM β) := by
  funext c s w
  unfold Core.liftIOCore
  cases h : x w with
  | ok a w1 =>
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, h, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read, instMonadEIO._aux_5, EST.Out.ok, EStateM.pure]
  | error e w1 =>
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, h, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read, instMonadEIO._aux_5, EST.Out.ok, EStateM.pure]

theorem liftM_bind_metaM {α β : Type} (x : IO α) (f : α → IO β) :
    (liftM (x >>= f) : MetaM β) = ((liftM x : MetaM α) >>= fun a => (liftM (f a) : MetaM β)) := by
  funext mctx mref cctx cref w
  simp only [liftM, monadLift, MonadLift.monadLift]
  show Core.liftIOCore (x >>= f) cctx cref w = ((Core.liftIOCore x : CoreM α) >>= fun a => Core.liftIOCore (f a)) cctx cref w
  rw [liftIOCore_bind]

/-- The profile block of Elab.lean 6973-6977 (five separate lifts) equals one lift of `profLogIO true`. -/
theorem profBlock_eq (s : String) :
    ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ =>
      (liftM h.flush : MetaM Unit)) = (liftM (profLogIO true s) : MetaM Unit) := by
  simp only [profLogIO, ↓reduceIte, liftM_bind_metaM]


/-! ## Diag: `LogMvK` is the field `logProf`; the 6973-6977 block and the 6423-6425 pair -/

theorem logMvK_of (M : MemoFamily O) : Tools.ShippingGen4KWalkEntry.LogMvK O :=
  fun _ _ hA b msg w hq => M.logProf hA b msg w hq

theorem profBlock_mv (M : MemoFamily O) {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx O.quiet mctx cctx)
    (s : String) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref
      ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ =>
      (liftM h.flush : MetaM Unit)) w) = mv w := by
  rw [profBlock_eq]
  exact M.logProf hA true s w hq

theorem stderrPair_mv (M : MemoFamily O) {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx O.quiet mctx cctx)
    (s : String) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) = mv w :=
  M.stderrLine hA s w hq


section PpDerive
variable (mctx : Meta.Context) (cctx : Core.Context)

theorem getEnv_run (w : Void IO.RealWorld) :
    ∃ w1, (getEnv : MetaM Environment) mctx mref cctx cref w = .ok (readOf cref w).env w1 := ⟨_, rfl⟩

theorem getMCtx_run (w : Void IO.RealWorld) :
    ∃ w1, (getMCtx : MetaM MetavarContext) mctx mref cctx cref w = .ok (readOf mref w).mctx w1 := ⟨_, rfl⟩

theorem getLCtx_run (w : Void IO.RealWorld) :
    (getLCtx : MetaM LocalContext) mctx mref cctx cref w = .ok mctx.lctx w := rfl

theorem getOptions_run (w : Void IO.RealWorld) :
    (getOptions : MetaM Options) mctx mref cctx cref w = .ok cctx.options w := rfl

theorem getCurrNamespace_run (w : Void IO.RealWorld) :
    (getCurrNamespace : MetaM Name) mctx mref cctx cref w = .ok cctx.currNamespace w := rfl

theorem getOpenDecls_run (w : Void IO.RealWorld) :
    (getOpenDecls : MetaM (List OpenDecl)) mctx mref cctx cref w = .ok cctx.openDecls w := rfl

theorem liftBaseIO_run {α : Type} (x : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', x w = .mk a w' ∧ (liftM x : MetaM α) mctx mref cctx cref w = .ok a w' := by
  cases hx : x w with
  | mk a w' =>
    refine ⟨a, w', rfl, ?_⟩
    simp only [liftM, monadLift, MonadLift.monadLift]
    show Core.liftIOCore x.toEIO cctx cref w = EST.Out.ok a w'
    unfold Core.liftIOCore
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, hx, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read,
      instMonadEIO._aux_5, EStateM.pure, BaseIO.toEIO]

theorem bind_ok {α β : Type} {m : MetaM α} {f : α → MetaM β} {w : Void IO.RealWorld} {a : α} {w1 : Void IO.RealWorld}
    (h : m mctx mref cctx cref w = .ok a w1) : (m >>= f) mctx mref cctx cref w = f a mctx mref cctx cref w1 := by
  simp [bind, ReaderT.bind, StateRefT'.instMonad._aux_13, instMonadEIO._aux_13, EST.bind, EStateM.bind, h]

theorem map_ok {α β : Type} {m : MetaM α} {g : α → β} {w : Void IO.RealWorld} {a : α} {w1 : Void IO.RealWorld}
    (h : m mctx mref cctx cref w = .ok a w1) : (g <$> m) mctx mref cctx cref w = .ok (g a) w1 := by
  change (m >>= fun a => pure (g a) : MetaM β) mctx mref cctx cref w = _
  rw [bind_ok mctx cctx h]; rfl

theorem getMCtx_endW (w : Void IO.RealWorld) :
    endW mctx mref cctx cref (getMCtx : MetaM MetavarContext) w = endW mctx mref cctx cref (get : MetaM Meta.State) w := rfl

open Tools.ShippingGen4KWalk in
theorem ppExpr_mv (M : MemoFamily O)
    (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref (Lean.Meta.ppExpr e) w) = mv w := by
  unfold Lean.Meta.ppExpr Lean.Meta.ppExprWithInfos Lean.Meta.getPPContext
  have M2 := M
  -- the two state reads
  have hf1 : mv (endW mctx mref cctx cref (getEnv : MetaM Environment) w) = mv w := M2.frame hA _ FramedNM.env w hq
  have hq1 : O.quiet (endW mctx mref cctx cref (getEnv : MetaM Environment) w) :=
    O.frameQ hA _ (framedNM_toA FramedNM.env) w hq
  have hf2 : mv (endW mctx mref cctx cref (getMCtx : MetaM MetavarContext)
      (endW mctx mref cctx cref (getEnv : MetaM Environment) w)) = mv (endW mctx mref cctx cref (getEnv : MetaM Environment) w) := by
    rw [getMCtx_endW mctx cctx]; exact M2.frame hA _ FramedNM.metaGet _ hq1
  let w1 := endW mctx mref cctx cref (getEnv : MetaM Environment) w
  let w2 := endW mctx mref cctx cref (getMCtx : MetaM MetavarContext) w1
  let ctx0 : PPContext :=
    { env := (readOf cref w).env, mctx := (readOf mref w1).mctx, lctx := Meta.Context.lctx mctx,
      opts := cctx.options, currNamespace := cctx.currNamespace, openDecls := cctx.openDecls }
  have hCB : (do
      let __do_lift ← getEnv
      let __do_lift_1 ← getMCtx
      let __do_lift_2 ← getLCtx
      let __do_lift_3 ← getOptions
      let __do_lift_4 ← getCurrNamespace
      let __do_lift_5 ← getOpenDecls
      pure { env := __do_lift, mctx := __do_lift_1, lctx := __do_lift_2, opts := __do_lift_3,
             currNamespace := __do_lift_4, openDecls := __do_lift_5 } : MetaM PPContext) mctx mref cctx cref w
      = .ok ctx0 w2 := rfl
  obtain ⟨a, w3, hx, hl⟩ := liftBaseIO_run mctx cctx (Lean.ppExprWithInfos ctx0 e) w2
  have hB := bind_ok mctx cctx (f := fun ctx => liftM (Lean.ppExprWithInfos ctx e)) hCB
  have hB' : ((do
      let __do_lift ← getEnv
      let __do_lift_1 ← getMCtx
      let __do_lift_2 ← getLCtx
      let __do_lift_3 ← getOptions
      let __do_lift_4 ← getCurrNamespace
      let __do_lift_5 ← getOpenDecls
      pure { env := __do_lift, mctx := __do_lift_1, lctx := __do_lift_2, opts := __do_lift_3,
             currNamespace := __do_lift_4, openDecls := __do_lift_5 } : MetaM PPContext) >>=
      fun ctx => (liftM (Lean.ppExprWithInfos ctx e) : MetaM FormatWithInfos)) mctx mref cctx cref w = .ok a w3 :=
    hB.trans hl
  have hM := map_ok mctx cctx (g := fun x => FormatWithInfos.fmt x) hB'
  have hend : endW mctx mref cctx cref ((fun x => FormatWithInfos.fmt x) <$> ((do
      let __do_lift ← getEnv
      let __do_lift_1 ← getMCtx
      let __do_lift_2 ← getLCtx
      let __do_lift_3 ← getOptions
      let __do_lift_4 ← getCurrNamespace
      let __do_lift_5 ← getOpenDecls
      pure { env := __do_lift, mctx := __do_lift_1, lctx := __do_lift_2, opts := __do_lift_3,
             currNamespace := __do_lift_4, openDecls := __do_lift_5 } : MetaM PPContext) >>=
      fun ctx => (liftM (Lean.ppExprWithInfos ctx e) : MetaM FormatWithInfos))) w = w3 := by
    unfold endW; rw [hM]
  have hm3 : mv w3 = mv w2 := by
    have := ((M.printersMv w hq ctx0 rfl).1 e) w2
    rw [hx] at this
    exact this
  refine Eq.trans (congrArg mv hend) ?_
  exact hm3.trans (hf2.trans hf1)

end PpDerive

theorem ppMvK_of (M : MemoFamily O) : Tools.ShippingGen4KWalkHelpers.PpMvK O :=
  fun mctx cctx hA e w hq => ppExpr_mv mctx cctx M hA e w hq


theorem profLogIO_false (s : String) : profLogIO false s = pure () := rfl

/-! ## Residual (NOT a family statement): the exception rendering at Elab.lean 6605 -/

/-- `ex.toMessageData.toString` of a message in the class `OkMsg` leaves the memo. `OkMsg`'s `withContext c` only asks
`OkEnv c.env` (the three refs), and `c` is the environment CAPTURED at throw time, not the current world's. -/
def MsgMvK (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ (m : MessageData), OkMsg m → ∀ w,
    O.quiet w → mv (endW mctx mref cctx cref (liftM m.toString : MetaM String) w) = mv w

end Tools.ShippingGen4KWalkDiag
