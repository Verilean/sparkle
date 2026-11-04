import Tools.Assume.MemoFamily
import Tools.ShippingChildKeeps
import Tools.ShippingGen4KWalk
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4KWalkHelpers
import Tools.ShippingGen5T1ND
import Tests.Gen4.MemoFamilyCheck
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
-- BUILT: kjob lake build Tests.Gen4.MemoFamilyRev3Check exit 0 (756 jobs, rt172, source as of 4dafaab4): MEMOFAMILY REV3 CHECK: TYPE 15/15 / MUTANT 11/11 / OUTSIDE 18/18 / AXIOMS 20 / CLOSURE 4 (+2 positive controls) / MODEL 1. Clean build is the coder's.
-- Scratch check for scripts/gen4/MEMO_FAMILY_FREEZE.md rev3 (does NOT edit Tools/Assume/MemoFamily.lean; its MemoTeleR3 / MemoFamilyR3 are the proposed rev3 types). No sorry, no axiom, no native_decide.

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


/-! ## ppExpr: the printer condition as a typed, memo-version of `OkEnv` -/

/-- A `BaseIO` action leaves what the memo cell reads (from every world). -/
def MvInert {α : Type} (x : BaseIO α) : Prop :=
  ∀ w, match x w with
    | .mk _ w' => readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w

/-- The memo version of `OkEnv`: the two printer entry points over this environment leave the memo as it was. -/
def OkEnvMv (env : Environment) : Prop :=
  ∀ ctx : PPContext, ctx.env = env →
    (∀ e : Lean.Expr, MvInert (ppExprWithInfos ctx e)) ∧ (∀ n : Name, MvInert (ppConstNameWithInfos ctx n))


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
  lamTelescopeT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
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
  printersMv : ∀ w, O.quiet w → OkEnvMv (readOf cref w).env
  tele : MemoTeleR3 O

/-! ## Replacement: the rev2 (`Keeps`) `lamTelescope` is derived from the Triple form -/

variable {O : RefLawsAOps MkRefd mref cref}

/-- Same statement as the rev2 field `MemoTele.lamTelescope`; derived from the Triple form (`Q = fun _ => I`, `R = I`). -/
theorem MemoTeleR3.lamTelescope (T : MemoTeleR3 O) : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) := by
  intro mctx cctx α I hA hIq htr e k cleanup hk
  exact keeps_iff.mpr (T.lamTelescopeT I (fun _ => I) I hA hIq (fun _ => hIq) hIq htr (fun _ => htr) htr e k cleanup
    (fun mctx' cctx' xs b hA' => keeps_iff.mp (hk mctx' cctx' xs b hA')))

theorem MemoTeleR3.toRev2 (T : MemoTeleR3 O) : MemoTele O where
  telescope := T.telescope
  lamTelescope := T.lamTelescope
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
  M.tele.lamTelescope (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) e k cleanup hk

/-- Tools/ShippingGen4KWalkLegacyTail.lean:84 (`M.tele.lamTelescope I _ hS.1 hS.2 _ _ _` in a `kwalkM` list), with `StableK`. -/
theorem replay_legacyTail {mctx : Meta.Context} {cctx : Core.Context} (M : MemoFamilyR3 O)
    {I : Void IO.RealWorld → Prop} (hS : Tools.ShippingGen4KWalkPrims.StableK O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
    {α : Type} (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) :=
  M.tele.lamTelescope I hA hS.1 hS.2 e k cleanup hk


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
theorem ppExpr_mv (M : MemoFamilyR3 O)
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
    have := ((M.printersMv w hq ctx0 rfl).1 e) w2
    rw [hx] at this
    exact this
  refine Eq.trans (congrArg mv hend) ?_
  exact hm3.trans (hf2.trans hf1)

end PpDerive

theorem ppMvK_of (M : MemoFamilyR3 O) : Tools.ShippingGen4KWalkHelpers.PpMvK O :=
  fun mctx cctx hA e w hq => ppExpr_mv mctx cctx M hA e w hq



theorem profLogIO_false (s : String) : profLogIO false s = pure () := rfl

/-! ## Residual (NOT a family statement): the exception rendering at Elab.lean 6605 -/

/-- `ex.toMessageData.toString` of a message in the class `OkMsg` leaves the memo. `OkMsg`'s `withContext c` only asks
`OkEnv c.env` (the three refs), and `c` is the environment CAPTURED at throw time, not the current world's. -/
def MsgMvK (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ (m : MessageData), OkMsg m → ∀ w,
    O.quiet w → mv (endW mctx mref cctx cref (liftM m.toString : MetaM String) w) = mv w

/-! ## Vacuous model (satisfiability of the TYPE only) -/
def vacO : RefLawsAOps MkRefd mref cref := RefLawsAOps.quietFalse MkRefd mref cref
theorem vacuous_model_R3 : MemoFamilyR3 (mref := mref) (cref := cref) vacO where
  frame := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoGet := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  memoSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  logProf := by intro _ _ _ _ _ _ hq; exact False.elim hq
  stderrLine := by intro _ _ _ _ _ hq; exact False.elim hq
  printersMv := by intro _ hq; exact False.elim hq
  tele :=
    { telescope := by intro _ _ _ I _ hIq _ _ _ _ w hw; exact False.elim (hIq w hw)
      lamTelescopeT := by intro _ _ _ P _ _ _ hPq _ _ _ _ _ _ _ _ _ w hw; exact False.elim (hPq w hw)
      localDecl := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      letDecl := by intro _ _ _ I _ hIq _ _ _ _ _ _ w hw; exact False.elim (hIq w hw) }

/-! ## Expected (written separately from the structure above; the other 11 statements are rev2's `Expected`) -/
namespace Expected
def lamTelescopeT (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    Tests.Gen4.MemoFamilyCheck.Expected.TeleI O P →
    (∀ a, Tests.Gen4.MemoFamilyCheck.Expected.TeleI O (Q a)) →
    Tests.Gen4.MemoFamilyCheck.Expected.TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      ∀ w, P w → match k xs b mctx' mref cctx' cref w with
        | .ok a w' => Q a w'
        | .error ex w' => R w' ∧ OkExc ex) →
    ∀ w, P w → match Lean.Meta.lambdaTelescope e k cleanup mctx mref cctx cref w with
      | .ok a w' => Q a w'
      | .error ex w' => R w' ∧ OkExc ex
def logProf (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (b : Bool) (msg : String) w,
    O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
def stderrLine (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (s : String) w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref
      ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ => (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) =
      readOf sparkleSubModuleCache w
def printersMv (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ w, O.quiet w → ∀ ctx : PPContext, ctx.env = (readOf cref w).env →
    (∀ e : Lean.Expr, ∀ v, match Lean.ppExprWithInfos ctx e v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v) ∧
    (∀ n : Name, ∀ v, match Lean.ppConstNameWithInfos ctx n v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v)
end Expected

/-! ## Mutants of the new / changed statements (signature/defeq rejections, NOT semantic counterexamples) -/
namespace Mutant
open Tests.Gen4.MemoFamilyCheck.Expected in
/-- L1: no `Q a w → quiet w`. -/
def L1 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
open Tests.Gen4.MemoFamilyCheck.Expected in
/-- L2: failure side without `OkExc`. -/
def L2 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun _ w => R w)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun _ w => R w)
open Tests.Gen4.MemoFamilyCheck.Expected in
/-- L3: no transfer premise for `R`. -/
def L3 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
open Tests.Gen4.MemoFamilyCheck.Expected in
/-- L4: the conclusion's success postcondition is `True`, not the continuation's `Q`. -/
def L4 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) (fun _ _ => True) (fun ex w => R w ∧ OkExc ex)
open Tests.Gen4.MemoFamilyCheck.Expected in
/-- L5: the rev2 `Keeps` statement (a different type: this is what the Triple form replaces). -/
def L5 (O : RefLawsAOps MkRefd mref cref) : Prop := Tests.Gen4.MemoFamilyCheck.Expected.lamTelescope O
open Tests.Gen4.MemoFamilyCheck.Expected in
/-- L6: no `P w → quiet w`. -/
def L6 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
/-- D1: logProf without `O.quiet w →`. -/
def D1 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (b : Bool) (msg : String) w,
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
/-- D2: stderrLine without the flush (the print alone). -/
def D2 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (s : String) w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (IO.eprintln s) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
/-- D3: printersMv without `O.quiet w →`. -/
def D3 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ w, ∀ ctx : PPContext, ctx.env = (readOf cref w).env →
    (∀ e : Lean.Expr, ∀ v, match Lean.ppExprWithInfos ctx e v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v) ∧
    (∀ n : Name, ∀ v, match Lean.ppConstNameWithInfos ctx n v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v)
/-- D4: printersMv with the three-ref class `OkEnv` in place of the memo class (a different, weaker-looking claim). -/
def D4 (O : RefLawsAOps MkRefd mref cref) : Prop := ∀ w, O.quiet w → OkEnv (readOf cref w).env
/-- D5: logProf without `AdmCtx`. -/
def D5 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, ∀ (b : Bool) (msg : String) w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
end Mutant

/-! ## Statements OUTSIDE the boundary: expressible Props that are NOT any new field's type -/
namespace Outside
/-- B1: an arbitrary path and mode. -/
def arbPath (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (p : System.FilePath) (m : IO.FS.Mode)
    (s : String) w, O.quiet w →
    mv (endW mctx mref cctx cref
      ((liftM (IO.FS.Handle.mk p m) : MetaM IO.FS.Handle) >>= fun h =>
        (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ => (liftM h.flush : MetaM Unit)) w) = mv w
/-- B2: `putStrLn` on an arbitrary handle. -/
def arbHandlePut (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (h : IO.FS.Handle) (s : String) w,
    O.quiet w → mv (endW mctx mref cctx cref (liftM (h.putStrLn s) : MetaM Unit) w) = mv w
/-- B3: `flush` on an arbitrary handle. -/
def arbHandleFlush (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (h : IO.FS.Handle) w,
    O.quiet w → mv (endW mctx mref cctx cref (liftM h.flush : MetaM Unit) w) = mv w
/-- B4: `flush` of an arbitrary stream (`IO.FS.Stream` is a structure of closures). -/
def arbStreamFlush (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (h : IO.FS.Stream) w,
    O.quiet w → mv (endW mctx mref cctx cref (liftM h.flush : MetaM Unit) w) = mv w
/-- B5: `ppExpr` of an arbitrary printer, unconditionally (this is `PpMvK`). -/
def arbPrinter (O : RefLawsAOps MkRefd mref cref) : Prop := Tools.ShippingGen4KWalkHelpers.PpMvK O
/-- B6: rendering a message of the class `OkMsg` (this is `MsgMvK`). -/
def msgRender (O : RefLawsAOps MkRefd mref cref) : Prop := MsgMvK O
end Outside

/-! ## The checker -/

private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) (opq : NameSet) :
    NameSet × NameSet :=
  match todo with
  | [] => (seen, opq)
  | n :: rest =>
    if seen.contains n then closure env rest seen opq else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen opq
    | some ci =>
      let (body, opq) : List Name × NameSet := match ci with
        | .thmInfo v => (v.value.getUsedConstants.toList, opq)
        | .defnInfo v => (v.value.getUsedConstants.toList, opq)
        | .opaqueInfo _ => ([], opq.insert n)
        | _ => ([], opq)
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen opq

private def forbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def closureBad (n : Name) : CoreM (List Name × Nat) := do
  let (seen, _) := closure (← getEnv) [n] {} {}
  return (seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m, seen.size)

private def fieldDefEq (field : Name) (E : Name) : MetaM Bool := do
  let info ← getConstInfo field
  forallBoundedTelescope info.type (some 4) fun xs body => do
    let some mrefF := xs[0]? | throwError "{field}: no mref"
    let some crefF := xs[1]? | throwError "{field}: no cref"
    let some oF := xs[2]? | throwError "{field}: no O"
    let lvls := (← getConstInfo E).levelParams.map fun _ => Level.zero
    isDefEq body (mkApp3 (mkConst E lvls) mrefF crefF oF)

elab "#memo_family_rev3_check" : command => liftTermElabM do
  let pre := `Tests.Gen4.MemoFamilyRev3Check
  let old := `Tests.Gen4.MemoFamilyCheck.Expected
  let fam := pre ++ `MemoFamilyR3
  let tele := pre ++ `MemoTeleR3
  let typeCases : List (Name × Name) :=
    [(fam ++ `frame, old ++ `frame), (fam ++ `frameCacheSet, old ++ `frameCacheSet),
     (fam ++ `frameDepthSet, old ++ `frameDepthSet), (fam ++ `memoGet, old ++ `memoGet),
     (fam ++ `memoSet, old ++ `memoSet), (fam ++ `memoModify, old ++ `memoModify),
     (fam ++ `frameCacheModify, old ++ `frameCacheModify), (fam ++ `frameDepthModify, old ++ `frameDepthModify),
     (tele ++ `telescope, old ++ `telescope), (tele ++ `localDecl, old ++ `localDecl), (tele ++ `letDecl, old ++ `letDecl),
     (tele ++ `lamTelescopeT, pre ++ `Expected ++ `lamTelescopeT), (fam ++ `logProf, pre ++ `Expected ++ `logProf),
     (fam ++ `stderrLine, pre ++ `Expected ++ `stderrLine), (fam ++ `printersMv, pre ++ `Expected ++ `printersMv)]
  let mutCases : List (String × Name × Name) :=
    [("L1", tele ++ `lamTelescopeT, `L1), ("L2", tele ++ `lamTelescopeT, `L2), ("L3", tele ++ `lamTelescopeT, `L3),
     ("L4", tele ++ `lamTelescopeT, `L4), ("L5", tele ++ `lamTelescopeT, `L5), ("L6", tele ++ `lamTelescopeT, `L6),
     ("D1", fam ++ `logProf, `D1), ("D2", fam ++ `stderrLine, `D2), ("D3", fam ++ `printersMv, `D3),
     ("D4", fam ++ `printersMv, `D4), ("D5", fam ++ `logProf, `D5)]
  let outCases : List Name := [`arbPath, `arbHandlePut, `arbHandleFlush, `arbStreamFlush, `arbPrinter, `msgRender]
  let newFields : List Name := [fam ++ `logProf, fam ++ `stderrLine, fam ++ `printersMv]
  -- TYPE
  let mut ok : Nat := 0
  for (f, e) in typeCases do
    unless ← fieldDefEq f e do throwError "TYPE mismatch for {f}"
    ok := ok + 1
  unless ok == 15 do throwError "TYPE count {ok} ≠ 15"
  -- MUTANT
  let mut rej : Nat := 0
  for (lbl, f, m) in mutCases do
    if ← fieldDefEq f (pre ++ `Mutant ++ m) then throwError "mutant {lbl} NOT rejected for {f}"
    rej := rej + 1
  -- OUTSIDE: expressible, not defeq to any of the 3 new fields (and not to each other's replacement)
  let mut outRej : Nat := 0
  for o in outCases do
    for f in newFields do
      if ← fieldDefEq f (pre ++ `Outside ++ o) then throwError "outside statement {o} IS the type of {f}"
      outRej := outRej + 1
  -- AXIOMS
  let audited : List Name :=
    [fam, tele, fam ++ `mk, tele ++ `mk, pre ++ `vacuous_model_R3, pre ++ `MemoTeleR3.lamTelescope,
     pre ++ `MemoTeleR3.toRev2, pre ++ `MemoFamilyR3.toRev2, pre ++ `logMvK_of, pre ++ `profBlock_eq,
     pre ++ `profBlock_mv, pre ++ `stderrPair_mv, pre ++ `profLogIO_false, pre ++ `ppExpr_mv, pre ++ `ppMvK_of,
     pre ++ `replay_keeps_KW_lambdaTelescope, pre ++ `replay_legacyTail, pre ++ `OkEnvMv, pre ++ `MvInert, pre ++ `MsgMvK]
  let mut axOk : Nat := 0
  for n in audited do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
    axOk := axOk + 1
  -- CLOSURE (of the TRUSTED structure and the two types it adds)
  let mut clOk : Nat := 0
  for n in [fam, tele, pre ++ `OkEnvMv, pre ++ `MvInert] do
    let (bad, _) ← closureBad n
    unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"
    clOk := clOk + 1
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let (bad, _) ← closureBad c
    if bad.isEmpty then throwError "closure detector MISSED {c}"
  -- MODEL
  let mi ← getConstInfo (pre ++ `vacuous_model_R3)
  unless mi.type.getUsedConstants.contains fam do throwError "vacuous_model_R3 does not state MemoFamilyR3"
  logInfo m!"MEMOFAMILY REV3 CHECK: TYPE {ok}/15 (11 unchanged vs rev2 Expected, 4 new/changed) / MUTANT {rej}/11 (signature/defeq rejections, not semantic counterexamples) / OUTSIDE {outRej}/18 (6 statements x 3 new fields, none defeq) / AXIOMS {axOk} standard-only / CLOSURE {clOk} clean (+2 positive controls) / MODEL 1 (vacuous quiet=False; type satisfiability only)"

#memo_family_rev3_check

end Tests.Gen4.MemoFamilyRev3Check
