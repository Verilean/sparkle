import Tools.ShippingGen5EnvFrame
set_option autoImplicit false
-- NOT BUILT: implementation of the U2 freeze (scripts/gen5/DG_ENV_T2_U2_FREEZE.md). Pod scratch compile only; Pod build and clean build are the coder's.

/-! # DG-ENV unit U2: `EnvFrameEnd` rows for class B' (IO lift) and class C, CONDITIONAL

Extends `Tools.ShippingGen5EnvFrame` (U1). Every row is stated at the `endW` (either outcome) form `EnvFrameEnd`.
The cell premises (`ReadWorld r`, `SetFrame r cref`, `SetGet cref`, `r.ref ≠ cref.ref`) stay HYPOTHESES of the lemmas: this is a
conditional algebra, NOT a supply of C0, and nothing here says the premises hold of the runtime.
No `Laws` / `RefLawsAOps` / `RefLawsATele` / `T1Hyp` / `T1HypND` field, no `GetEnvFrame`, `EnvSnapshot`,
`getEnvFrame_of_readKeeps` or `envFrame_getConstInfo` is used. No new law, no shared-definition change.

Rows: auxiliary A1-A3; B' U2-1..U2-4 (`liftM` of an `IO` ref operation is `rfl`-equal to the `MetaM` operation, so they are the U1 lemmas);
C U2-5..U2-10 (metaGet, metaModify, coreModifyTrace, freshFVar, fvarThrowUnknown, constInfo). All 10 rows of the freeze closed;
no row was dropped. `SetGet cref` is used by A3 (hence U2-7, U2-8) because those are writers of `cref` itself, so `SetFrame`
cannot be used; this statement is about THIS proof route only, not a claim that no other route exists.
The `constInfo` error path (`throwUnknownConstant`, `mkUnknownIdentifierMessage`, `throwErrorAt` = `withRef` + `throwError`) is proved
for the whole `endW` result (ok and error). One private helper `envFrameEnd_withRef` (a context change, general in `cctx`) is added
beyond the freeze's 13 items; the closure audit covers it as it is reached from U2-10.
Audit: Tests/Gen5/EnvFrame2Check.lean. -/
namespace Tools.ShippingGen5EnvFrame2
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (endW readOf)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame SetGet getW setW)
open Tools.ShippingGen5EnvFrame (EnvFrameEnd envFrameEnd_pure envFrameEnd_bind envFrameEnd_get envFrameEnd_set
  envFrameEnd_modify envFrameEnd_modifyGet envFrameEnd_getEnv)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- (A1) -/
theorem envFrameEnd_keep {α : Type} {x : MetaM α}
    (h : ∀ w, endW mctx mref cctx cref x w = w) : EnvFrameEnd x mctx mref cctx cref := by
  intro w
  rw [h w]

/-- (A3) -/
theorem envFrameEnd_coreModifyGet {β : Type} (g : Core.State → β × Core.State)
    (henv : ∀ s, (g s).2.env = s.env) (hc : ReadWorld cref) (hs : SetGet cref) :
    EnvFrameEnd (ST.Ref.modifyGet cref g : MetaM β) mctx mref cctx cref := by
  intro w
  have hw : endW mctx mref cctx cref (ST.Ref.modifyGet cref g : MetaM β) w =
      setW cref (g (readOf cref w)).2 (getW cref w) := by
    unfold endW setW getW readOf
    rfl
  rw [hw, hc w]
  unfold envAt
  rw [hs, henv]

/-- (U2-5) -/
theorem envFrameEnd_metaGet (hm : ReadWorld mref) :
    EnvFrameEnd (get : MetaM Meta.State) mctx mref cctx cref :=
  envFrameEnd_get (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) hm

/-- (A2) -/
theorem envFrameEnd_throwError {α : Type} (msg : MessageData) (hc : ReadWorld cref) (hm : ReadWorld mref) :
    EnvFrameEnd (Lean.throwError msg : MetaM α) mctx mref cctx cref := by
  unfold Lean.throwError
  refine envFrameEnd_bind (envFrameEnd_keep fun w => rfl) fun ref => ?_
  refine envFrameEnd_bind ?_ fun p => ?_
  · show EnvFrameEnd (do let m ← Lean.addMessageContextFull msg; pure (ref, m) : MetaM _) mctx mref cctx cref
    refine envFrameEnd_bind ?_ fun _ => envFrameEnd_pure _
    unfold Lean.addMessageContextFull
    refine envFrameEnd_bind (envFrameEnd_getEnv hc) fun env => ?_
    refine envFrameEnd_bind ?_ fun mc => ?_
    · exact envFrameEnd_bind (envFrameEnd_metaGet hm) fun _ => envFrameEnd_pure _
    refine envFrameEnd_bind (envFrameEnd_keep fun w => rfl) fun lc => ?_
    refine envFrameEnd_bind (envFrameEnd_keep fun w => rfl) fun o => ?_
    exact envFrameEnd_pure _
  · exact envFrameEnd_keep fun w => rfl

/-- (U2-1) -/
theorem envFrameEnd_getIO {σ : Type} {r : IO.Ref σ} (hr : ReadWorld r) :
    EnvFrameEnd (liftM (ST.Ref.get r : IO σ) : MetaM σ) mctx mref cctx cref :=
  Tools.ShippingGen5EnvFrame.envFrameEnd_get hr
/-- (U2-2) -/
theorem envFrameEnd_setIO {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref)
    (hf : SetFrame r cref) : EnvFrameEnd (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit) mctx mref cctx cref :=
  Tools.ShippingGen5EnvFrame.envFrameEnd_set v hne hf
/-- (U2-3) -/
theorem envFrameEnd_modifyIO {σ : Type} {r : IO.Ref σ} (f : σ → σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit) mctx mref cctx cref :=
  envFrameEnd_modify f hr hne hf
/-- (U2-4) -/
theorem envFrameEnd_modifyGetIO {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β) mctx mref cctx cref :=
  envFrameEnd_modifyGet f hr hne hf
/-- (U2-6) -/
theorem envFrameEnd_metaModify (f : Meta.State → Meta.State) (hm : ReadWorld mref)
    (hne : mref.ref ≠ cref.ref) (hf : SetFrame mref cref) :
    EnvFrameEnd (modify f : MetaM Unit) mctx mref cctx cref :=
  envFrameEnd_modify (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) f hm hne hf
/-- (U2-7) -/
theorem envFrameEnd_coreModifyTrace (f : TraceState → TraceState) (hc : ReadWorld cref) (hs : SetGet cref) :
    EnvFrameEnd (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit) mctx mref cctx cref :=
  envFrameEnd_coreModifyGet (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    (fun s => ((), {s with traceState := f s.traceState})) (fun _ => rfl) hc hs
/-- (U2-8) -/
theorem envFrameEnd_freshFVar (hc : ReadWorld cref) (hs : SetGet cref) :
    EnvFrameEnd (mkFreshFVarId : MetaM FVarId) mctx mref cctx cref := by
  unfold mkFreshFVarId mkFreshId
  refine envFrameEnd_bind (m := (do
    let ngen ← getNGen
    setNGen ngen.next
    pure ngen.curr : MetaM Name)) ?_ fun r => envFrameEnd_pure _
  refine envFrameEnd_bind (m := (getNGen : MetaM NameGenerator)) ?_ fun ngen => ?_
  · show EnvFrameEnd (do let s ← (ST.Ref.get cref : MetaM Core.State); pure s.ngen : MetaM NameGenerator) mctx mref cctx cref
    exact envFrameEnd_bind (envFrameEnd_get (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) hc)
      fun s => envFrameEnd_pure s.ngen
  refine envFrameEnd_bind (m := (setNGen ngen.next : MetaM Unit)) ?_ fun _ => envFrameEnd_pure _
  exact envFrameEnd_coreModifyGet (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    (fun s => ((), {s with ngen := ngen.next})) (fun _ => rfl) hc hs
/-- (U2-9) -/
theorem envFrameEnd_fvarThrowUnknown {α : Type} (id : FVarId) (hc : ReadWorld cref) :
    EnvFrameEnd (liftM (id.throwUnknown : CoreM α) : MetaM α) mctx mref cctx cref := by
  intro w
  have key : ∃ e, (liftM (id.throwUnknown : CoreM α) : MetaM α) mctx mref cctx cref w
      = EST.Out.error e (getW cref w) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := key
  unfold endW
  rw [he]
  dsimp only
  rw [hc w]

private theorem envFrameEnd_withRef {α : Type} (ref : Syntax) {x : MetaM α}
    (h : ∀ c : Core.Context, EnvFrameEnd x mctx mref c cref) :
    EnvFrameEnd (withRef ref x : MetaM α) mctx mref cctx cref := by
  unfold withRef
  refine envFrameEnd_bind (envFrameEnd_keep fun w => rfl) fun old => ?_
  intro w
  exact h _ w

/-- (U2-10) -/
theorem envFrameEnd_constInfo (n : Name) (hc : ReadWorld cref) (hm : ReadWorld mref) :
    EnvFrameEnd (getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref := by
  unfold getConstInfo
  refine envFrameEnd_bind (envFrameEnd_getEnv hc) fun env => ?_
  cases h : env.find? n with
  | some info => exact envFrameEnd_pure _
  | none =>
    show EnvFrameEnd (throwUnknownConstant n : MetaM ConstantInfo) mctx mref cctx cref
    unfold throwUnknownConstant throwUnknownConstantAt throwUnknownIdentifierAt
    refine envFrameEnd_bind (envFrameEnd_keep fun w => rfl) fun ref => ?_
    refine envFrameEnd_bind ?_ fun m => ?_
    · unfold mkUnknownIdentifierMessage mkUnknownIdentifierMessageCore
      refine envFrameEnd_bind ?_ fun _ => envFrameEnd_pure _
      refine envFrameEnd_bind (envFrameEnd_getEnv hc) fun env' => ?_
      split <;> exact envFrameEnd_pure _
    · unfold Lean.throwErrorAt
      exact envFrameEnd_withRef _ fun c => envFrameEnd_throwError _ hc hm

end Tools.ShippingGen5EnvFrame2

#print axioms Tools.ShippingGen5EnvFrame2.envFrameEnd_constInfo
#print axioms Tools.ShippingGen5EnvFrame2.envFrameEnd_freshFVar
