import Tools.ShippingGen5EnvFrame2
import Tools.ShippingGen5EnvQ
import Tools.ShippingChildFresh
set_option autoImplicit false
-- Built: clean issue-linked build env9v-fe5c28aa exit 0, 756 jobs, approved at fe5c28aa (unit U3, freeze r9 scripts/gen5/DG_ENV_T2_U3_FREEZE.md). Conditional result; not DG-ENV / C0 / FG completion. No sorry / axiom / native_decide.

/-! # DG-ENV unit U3: per-field aggregation of the closed `FramedA` rows, CONDITIONAL

Extends `Tools.ShippingGen5EnvFrame2` (U2) and `Tools.ShippingGen5EnvQ`. Every theorem is conditional: `CellPrem`
(the named cell premises of U1 / U2), `QuietStrength L L' env₀` and `AdmDown L L'` are HYPOTHESES. `L'` is not built, C0 is not supplied,
nothing here says the premises hold of the runtime. No new law, no `Laws` / `RefLawsAOps` / `RefLawsATele` field, no TRUSTED boundary,
no shared-definition change.

E1-E4 are law-free (E4 is stated for an arbitrary quiet predicate). The 8 F theorems use exactly `Laws.O`, `RefLawsAOps.quiet` and the
one `RefLawsAOps` field of their row (the audit checks this). The 13 class-D constructors (`DRow`), `Diag` and the four telescope fields are NOT served:
this route supplies nothing for them. `40 - 13 = 27` is a constructor count, not a non-overlap or supplier statement.
Audit: Tests/Gen5/EnvFrame3Check.lean. -/
namespace Tools.ShippingGen5EnvFrame3
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW endW_of_runs Throws Op SideRef LocalRefType OkExc)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA (FramedA AdmCtx admCtx_none)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame SetGet)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame (EnvFrameEnd readsAt_endW)
open Tools.ShippingGen5EnvQ (QuietStrength AdmDown quiet_down)
open Tools.ShippingGen2 (Laws)
open Sparkle.Compiler.Elab (sparkleChildCache sparkleChildSynth sparkleSynthDepth)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (D1) the 13 class-D constructors of `FramedA`, with the same result types. -/
inductive DRow : {α : Type} → MetaM α → Prop
  | ioEnv (n : String) : DRow (liftM (IO.getEnv n) : MetaM _)
  | monoMs : DRow (liftM IO.monoMsNow : MetaM Nat)
  | mkExprCache (v : Lean.ExprStructMap String) : DRow (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
  | localMk {σ : Type} (v : σ) : LocalRefType σ → DRow (liftM (IO.mkRef v) : MetaM (IO.Ref σ))
  | whnf (e : Lean.Expr) : DRow (Lean.Meta.whnf e)
  | inferType (e : Lean.Expr) : DRow (Lean.Meta.inferType e)
  | isClass? (e : Lean.Expr) : DRow (Lean.Meta.isClass? e)
  | whnfUntil (e : Lean.Expr) (n : Name) : DRow (Lean.Meta.whnfUntil e n)
  | instantiateForall (e : Lean.Expr) (ps : Array Lean.Expr) : DRow (Lean.Meta.instantiateForall e ps)
  | mkLambdaFVars (xs : Array Lean.Expr) (e : Lean.Expr) (usedOnly usedLetOnly etaReduce generalizeNondepLet : Bool)
      (bi : BinderInfo) :
      DRow (Lean.Meta.mkLambdaFVars xs e usedOnly usedLetOnly etaReduce generalizeNondepLet bi)
  | mkAppM (c : Name) (xs : Array Lean.Expr) : DRow (Lean.Meta.mkAppM c xs)
  | unfoldDefinition? (e : Lean.Expr) : DRow (Lean.Meta.unfoldDefinition? e)
  | reduce (e : Lean.Expr) (explicitOnly skipTypes skipProofs : Bool) :
      DRow (Lean.Meta.reduce e explicitOnly skipTypes skipProofs)

/-- (D2) the three cell premises of one ref, as in U1 / U2. -/
def CellOK {σ : Type} (cref : ST.Ref IO.RealWorld Core.State) (r : IO.Ref σ) : Prop :=
  ReadWorld r ∧ r.ref ≠ cref.ref ∧ SetFrame r cref

/-- (D3) the cell premises the closed rows use, bundled under one name (existing premise names only; NOT supplied for the runtime). -/
def CellPrem (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  CellOK cref sparkleChildCache ∧ CellOK cref sparkleChildSynth ∧ CellOK cref sparkleSynthDepth ∧
  (∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) ∧
  (∀ (σ : Type) (r : IO.Ref σ), Fresh σ r → CellOK cref r) ∧
  ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref ∧ SetGet cref

/-- (E1) -/
theorem drow_toFramedA {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α} (h : DRow p) : FramedA Fresh p := by
  cases h with
  | ioEnv n => exact .ioEnv n
  | monoMs => exact .monoMs
  | mkExprCache v => exact .mkExprCache v
  | localMk v h => exact .localMk v h
  | whnf e => exact .whnf e
  | inferType e => exact .inferType e
  | isClass? e => exact .isClass? e
  | whnfUntil e n => exact .whnfUntil e n
  | instantiateForall e ps => exact .instantiateForall e ps
  | mkLambdaFVars xs e a b c d bi => exact .mkLambdaFVars xs e a b c d bi
  | mkAppM c xs => exact .mkAppM c xs
  | unfoldDefinition? e => exact .unfoldDefinition? e
  | reduce e a b c => exact .reduce e a b c

/-- (E2) -/
theorem envFrameEnd_framedA {Fresh : (σ : Type) → IO.Ref σ → Prop} (hcell : CellPrem Fresh mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α} (hp : FramedA Fresh p) (hnd : ¬ DRow p) :
    EnvFrameEnd p mctx mref cctx cref := by
  obtain ⟨hC, hS, hD, hSide, hFresh, hm, hmf, hmne, hc, hsg⟩ := hcell
  open Tools.ShippingGen5EnvFrame Tools.ShippingGen5EnvFrame2 in
  cases hp with
  | cacheGet => exact envFrameEnd_get hC.1
  | synthGet => exact envFrameEnd_get hS.1
  | depthGet => exact envFrameEnd_get hD.1
  | sideGet h => exact envFrameEnd_get (hSide _ h).1
  | sideSet v h => exact envFrameEnd_set v (hSide _ h).2.1 (hSide _ h).2.2
  | sideModify f h => exact envFrameEnd_modify f (hSide _ h).1 (hSide _ h).2.1 (hSide _ h).2.2
  | sideModifyGet f h => exact envFrameEnd_modifyGet f (hSide _ h).1 (hSide _ h).2.1 (hSide _ h).2.2
  | sideModifyGetIO f h => exact envFrameEnd_modifyGetIO f (hSide _ h).1 (hSide _ h).2.1 (hSide _ h).2.2
  | sideGetIO h => exact envFrameEnd_getIO (hSide _ h).1
  | sideSetIO v h => exact envFrameEnd_setIO v (hSide _ h).2.1 (hSide _ h).2.2
  | sideModifyIO f h => exact envFrameEnd_modifyIO f (hSide _ h).1 (hSide _ h).2.1 (hSide _ h).2.2
  | ioEnv n => exact absurd (.ioEnv n) hnd
  | constInfo n => exact envFrameEnd_constInfo n hc hm
  | env => exact envFrameEnd_getEnv hc
  | fvarThrowUnknown id => exact envFrameEnd_fvarThrowUnknown id hc
  | whnf e => exact absurd (.whnf e) hnd
  | inferType e => exact absurd (.inferType e) hnd
  | isClass? e => exact absurd (.isClass? e) hnd
  | whnfUntil e n => exact absurd (.whnfUntil e n) hnd
  | instantiateForall e ps => exact absurd (.instantiateForall e ps) hnd
  | mkLambdaFVars xs e a b c d bi => exact absurd (.mkLambdaFVars xs e a b c d bi) hnd
  | mkAppM c xs => exact absurd (.mkAppM c xs) hnd
  | unfoldDefinition? e => exact absurd (.unfoldDefinition? e) hnd
  | reduce e a b c => exact absurd (.reduce e a b c) hnd
  | metaGet => exact envFrameEnd_metaGet hm
  | coreModifyTrace f => exact envFrameEnd_coreModifyTrace f hc hsg
  | metaModify f => exact envFrameEnd_metaModify f hm hmne hmf
  | freshFVar => exact envFrameEnd_freshFVar hc hsg
  | monoMs => exact absurd .monoMs hnd
  | mkExprCache v => exact absurd (.mkExprCache v) hnd
  | exprCacheGet r h => exact envFrameEnd_get (hFresh _ r h).1
  | exprCacheGetIO r h => exact envFrameEnd_getIO (hFresh _ r h).1
  | localMk v h => exact absurd (.localMk v h) hnd
  | localGet r h hf => exact envFrameEnd_get (hFresh _ r hf).1
  | localSet r v h hf => exact envFrameEnd_set v (hFresh _ r hf).2.1 (hFresh _ r hf).2.2
  | localModify r f h hf => exact envFrameEnd_modify f (hFresh _ r hf).1 (hFresh _ r hf).2.1 (hFresh _ r hf).2.2
  | localGetIO r h hf => exact envFrameEnd_getIO (hFresh _ r hf).1
  | localSetIO r v h hf => exact envFrameEnd_setIO v (hFresh _ r hf).2.1 (hFresh _ r hf).2.2
  | localModifyIO r f h hf => exact envFrameEnd_modifyIO f (hFresh _ r hf).1 (hFresh _ r hf).2.1 (hFresh _ r hf).2.2
  | exprCacheModify r f hf => exact envFrameEnd_modify f (hFresh _ r hf).1 (hFresh _ r hf).2.1 (hFresh _ r hf).2.2

/-- (E3) -/
theorem envFrameEnd_throws {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α}
    (hp : Throws p) (hc : ReadWorld cref) (hm : ReadWorld mref) : EnvFrameEnd p mctx mref cctx cref := by
  cases hp with
  | err msg => exact Tools.ShippingGen5EnvFrame2.envFrameEnd_throwError msg hc hm
  | coreErr msg =>
    intro w
    have key : ∃ e, (liftM (throwError msg : CoreM α) : MetaM α) mctx mref cctx cref w
        = EST.Out.error e (Tools.ShippingStRefCorrespondence.getW cref w) := ⟨_, rfl⟩
    obtain ⟨e, he⟩ := key
    unfold endW
    rw [he]
    dsimp only
    rw [hc w]

/-- (E4) -/
theorem admCtx_down_of_none {q q' : Void IO.RealWorld → Prop} {mctx : Meta.Context} {cctx : Core.Context}
    (h : mctx.canUnfold? = none) : AdmCtx q' mctx cctx → AdmCtx q mctx cctx :=
  fun _ => admCtx_none h

/-- (F-frameT, row 2) -/
theorem frameT_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, L'.O.quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ L'.O.quiet (endW mctx mref cctx cref p w) := by
  intro mctx cctx α adm p hp w hw
  obtain ⟨hLw, hRA⟩ := (hq w).mp hw
  have H := L.O.frameT (hd _ _ adm) p hp w hLw
  exact ⟨H.1, (hq _).mpr ⟨H.2, readsAt_endW (envFrameEnd_throws hp hcell.2.2.2.2.2.2.2.2.1 hcell.2.2.2.2.2.1) hRA⟩⟩

/-- (F-excOk, row 3) -/
theorem excOk_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', L'.O.quiet w → p mctx mref cctx cref w = .error e w' → OkExc e := by
  intro mctx cctx α adm p hp w e w' hw h
  exact L.O.excOk (hd _ _ adm) p hp w e w' (quiet_down hq hw) h

/-- (F-frameQ, row 4; the 27 non-D rows) -/
theorem frameQ_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ¬ DRow p → ∀ w, L'.O.quiet w →
    L'.O.quiet (endW mctx mref cctx cref p w) := by
  intro mctx cctx α adm p hp hnd w hw
  obtain ⟨hLw, hRA⟩ := (hq w).mp hw
  exact (hq _).mpr ⟨L.O.frameQ (hd _ _ adm) p hp w hLw, readsAt_endW (envFrameEnd_framedA hcell hp hnd) hRA⟩

/-- (F-cacheSetQ, row 5) -/
theorem cacheSetQ_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w → L'.O.quiet w' := by
  intro mctx cctx adm v w u w' hr hw
  obtain ⟨hLw, hRA⟩ := (hq w).mp hw
  have hf : EnvFrameEnd (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref :=
    Tools.ShippingGen5EnvFrame.envFrameEnd_set v hcell.1.2.1 hcell.1.2.2
  have he := endW_of_runs hr
  refine (hq _).mpr ⟨L.O.cacheSetQ (hd _ _ adm) v w u w' hr hLw, ?_⟩
  rw [← he]
  exact readsAt_endW hf hRA

/-- (F-depthSetQ, row 6) -/
theorem depthSetQ_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    L'.O.quiet w → L'.O.quiet w' := by
  intro mctx cctx adm v w u w' hr hw
  obtain ⟨hLw, hRA⟩ := (hq w).mp hw
  have hf : EnvFrameEnd (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref :=
    Tools.ShippingGen5EnvFrame.envFrameEnd_set v hcell.2.2.1.2.1 hcell.2.2.1.2.2
  have he := endW_of_runs hr
  refine (hq _).mpr ⟨L.O.depthSetQ (hd _ _ adm) v w u w' hr hLw, ?_⟩
  rw [← he]
  exact readsAt_endW hf hRA

/-- (F-frame, row 7) -/
theorem frame_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ∀ w, L'.O.quiet w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w := by
  intro mctx cctx α adm p hp w hw
  exact L.O.frame (hd _ _ adm) p hp w (quiet_down hq hw)

/-- (F-cacheSet, row 8) -/
theorem cacheSet_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w := by
  intro mctx cctx adm v w u w' hr hw
  exact L.O.cacheSet (hd _ _ adm) v w u w' hr (quiet_down hq hw)

/-- (F-depthSet, row 9) -/
theorem depthSet_plus (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') :
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    L'.O.quiet w →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v := by
  intro mctx cctx adm v w u w' hr hw
  exact L.O.depthSet (hd _ _ adm) v w u w' hr (quiet_down hq hw)

end Tools.ShippingGen5EnvFrame3

#print axioms Tools.ShippingGen5EnvFrame3.frameQ_plus
#print axioms Tools.ShippingGen5EnvFrame3.envFrameEnd_framedA
