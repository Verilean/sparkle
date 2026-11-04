import Tools.Assume.MemoFamily
import Tools.ShippingChildKeeps
import Tools.ShippingGen4KWalk
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4KWalkHelpers
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
-- NOT BUILT (scratch, rt172): scratch check for scripts/gen4/MEMO_FAMILY_FREEZE.md rev3.

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildBndCore Tools.Assume.MemoFamily
open Sparkle.Compiler.Elab

namespace Tests.Gen4.MemoFamilyRev3Check

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

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


/-! ## Rev3 types (scratch copy of the proposed `MemoTele` / `MemoFamily`; `FramedNM`, `SideRefNM`, `mv` are the approved
rev2 ones from `Tools.Assume.MemoFamily`) -/

structure MemoTeleR3 (O : RefLawsAOps MkRefd mref cref) : Prop where
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      P w → P w') →
    (∀ a w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      Q a w → Q a w') →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      R w → R w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

structure MemoFamilyR3 (O : RefLawsAOps MkRefd mref cref) : Prop where
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {α : Type} (p : MetaM α), FramedNM MkRefd p → ∀ w, O.quiet w →
    mv (endW mctx mref cctx cref p w) = mv w
  frameCacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  frameDepthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  memoGet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ m w w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' → O.quiet w → mv w' = mv w
  memoSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = v
  memoModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    mv w' = f (mv w)
  frameCacheModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  frameDepthModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    mv w' = mv w
  logProf : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (b : Bool) (msg : String) w, O.quiet w →
    mv (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) = mv w
  stderrLine : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (s : String) w, O.quiet w →
    mv (endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) = mv w
  tele : MemoTeleR3 O

/-! ## Replacement: the rev2 (`Keeps`) `lamTelescope` is derived from the Triple form -/

variable {O : RefLawsAOps MkRefd mref cref}

/-- Same statement as the rev2 field `MemoTele.lamTelescope`; derived from the Triple form (`Q = fun _ => I`, `R = I`). -/
theorem MemoTeleR3.lamTelescopeKeeps (T : MemoTeleR3 O) : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) := by
  intro mctx cctx α I hA hIq htr e k cleanup hk
  exact keeps_iff.mpr (T.lamTelescope I (fun _ => I) I hA hIq (fun _ => hIq) hIq htr (fun _ => htr) htr e k cleanup
    (fun mctx' cctx' xs b hA' => keeps_iff.mp (hk mctx' cctx' xs b hA')))

theorem MemoTeleR3.toRev2 (T : MemoTeleR3 O) : MemoTele O where
  telescope := T.telescope
  lamTelescope := T.lamTelescopeKeeps
  localDecl := T.localDecl
  letDecl := T.letDecl

/-- Every rev2 statement follows from rev3 (so every consumer of `MemoFamily O` accepts a `MemoFamilyR3 O`). -/
theorem MemoFamilyR3.toRev2 (M : MemoFamilyR3 O) : MemoFamily O where
  frame := M.frame
  frameCacheSet := M.frameCacheSet
  frameDepthSet := M.frameDepthSet
  memoGet := M.memoGet
  memoSet := M.memoSet
  memoModify := M.memoModify
  frameCacheModify := M.frameCacheModify
  frameDepthModify := M.frameDepthModify
  tele := M.tele.toRev2

/-! ## Diag: `LogMvK` is the field `logProf`; the 6973-6977 block and the 6423-6425 pair -/

theorem logMvK_of (M : MemoFamilyR3 O) : Tools.ShippingGen4KWalkEntry.LogMvK O :=
  fun _ _ hA b msg w hq => M.logProf hA b msg w hq

theorem profBlock_mv (M : MemoFamilyR3 O) {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx O.quiet mctx cctx)
    (s : String) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref
      ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ =>
      (liftM h.flush : MetaM Unit)) w) = mv w := by
  rw [profBlock_eq]
  exact M.logProf hA true s w hq

theorem stderrPair_mv (M : MemoFamilyR3 O) {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx O.quiet mctx cctx)
    (s : String) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) = mv w :=
  M.stderrLine hA s w hq

/-! ## Replay of the existing `lamTelescope` use sites against `MemoFamilyR3` (text of the use site, `M : MemoFamilyR3 O`) -/

open Tools.ShippingGen4KWalk in
/-- Tools/ShippingGen4KWalk.lean:296 (`keeps_KW_lambdaTelescope`), unchanged text. -/
theorem replay_keeps_KW_lambdaTelescope {mctx : Meta.Context} {cctx : Core.Context}
    (M : MemoFamilyR3 O) (hA : AdmCtx O.quiet mctx cctx) (P) {α : Type}
    (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref (KW O P) (k xs b)) :
    Keeps mctx mref cctx cref (KW O P) (Lean.Meta.lambdaTelescope e k cleanup) :=
  M.tele.lamTelescopeKeeps (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) e k cleanup hk

/-- Tools/ShippingGen4KWalkLegacyTail.lean:84 (`M.tele.lamTelescope I _ hS.1 hS.2 _ _ _` in a `kwalkM` list), with `StableK`. -/
theorem replay_legacyTail {mctx : Meta.Context} {cctx : Core.Context} (M : MemoFamilyR3 O)
    {I : Void IO.RealWorld → Prop} (hS : Tools.ShippingGen4KWalkPrims.StableK O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
    {α : Type} (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) :=
  M.tele.lamTelescopeKeeps I hA hS.1 hS.2 e k cleanup hk


/-! ## ppExpr: the printer condition as a typed, memo-version of `OkEnv` -/

/-- A `BaseIO` action leaves what the memo cell reads (from every world). -/
def MvInert {α : Type} (x : BaseIO α) : Prop :=
  ∀ w, match x w with
    | .mk _ w' => readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w

/-- The memo version of `OkEnv`: the two printer entry points over this environment leave the memo as it was. -/
def OkEnvMv (env : Environment) : Prop :=
  ∀ ctx : PPContext, ctx.env = env →
    (∀ e : Lean.Expr, MvInert (ppExprWithInfos ctx e)) ∧ (∀ n : Name, MvInert (ppConstNameWithInfos ctx n))

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
theorem ppExpr_mv (M : MemoFamilyR3 O) (hpr : ∀ w, O.quiet w → OkEnvMv (readOf cref w).env)
    (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref (Lean.Meta.ppExpr e) w) = mv w := by
  unfold Lean.Meta.ppExpr Lean.Meta.ppExprWithInfos Lean.Meta.getPPContext
  have M2 := M.toRev2
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
    have := ((hpr w hq ctx0 rfl).1 e) w2
    rw [hx] at this
    exact this
  refine Eq.trans (congrArg mv hend) ?_
  exact hm3.trans (hf2.trans hf1)

end PpDerive

end Tests.Gen4.MemoFamilyRev3Check
