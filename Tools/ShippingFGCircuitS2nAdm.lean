import Tools.ShippingFGCircuitS2mReach3
set_option autoImplicit false
-- FG circuit pilot S2n: the callback-admissibility bridge `AdmDownR` of S2m. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §40.
-- (A) the context-carried form `AdmBoth` (original AND strengthened admissibility), established at the root and preserved by the context updates, and the strengthened operations laws `OpsB` derived on `AdmBoth` contexts WITHOUT `AdmDownR` (`opsB`, the S2m `ropsR` fields with `hdown` gone);
-- (B) where `AdmDownR` still enters: the S2h chain (`RefLawsAOps`, `hft_closesAtH`, ...) takes ONE bundle whose contexts are `AdmCtx bundle.quiet`; the bundle with `quiet := quietR` therefore needs `AdmCtx quietR → AdmCtx O.quiet` (`admBoth_of_down`: `AdmDownR` is exactly what turns a bundle context into an `AdmBoth` one);
-- (C) a world-level replacement `QuietCover` (every `O.quiet` world reads `e` and is reached from `w₀`) under which `AdmDownR`, `DRowEnvR`, `DiagEnvR`, `TeleR` and the root `hadm` are all THEOREMS: `hftCoreCloses_of_kidsR'` (hdown replaced) and `hftCoreCloses_of_cover` (7 premises -> `hcover hs h0`). The premise `QuietCover` is about the quiet predicate of the laws, not about callbacks.

namespace Tools.ShippingFGCircuitS2nAdm
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Diag Throws)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem DRow envFrameEnd_framedA envFrameEnd_throws)
open Tools.ShippingGen5EnvFrame (readsAt_endW)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitCover (RootReader)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingFGCircuitS2dKids (HftKidsGates)
open Tools.ShippingFGCircuitS1kStmt (hftHttp hftTlp)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

section Both
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The context-carried form**: a context is `AdmBoth` when its callback is inert for the plain quiet predicate AND for the strengthened one (both admissibilities, kept together; nothing is implied from one to the other). -/
def AdmBoth (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : Void IO.RealWorld)
    (mctx : Meta.Context) (cctx : Core.Context) : Prop :=
  AdmCtx O.quiet mctx cctx ∧ AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx

variable {O : RefLawsAOps MkRefd mref cref} {e : Environment} {w₀ : Void IO.RealWorld}
  {mctx : Meta.Context} {cctx : Core.Context}

/-- established at a context without a `canUnfold?` callback (the root context `mkMetaContext`: `mkMetaContext_canUnfold`) -/
theorem admBoth_none (h : mctx.canUnfold? = none) : AdmBoth O e w₀ mctx cctx :=
  ⟨admCtx_none h, admCtx_none h⟩

/-- the root context of the compile (`mkMetaContext`) is `AdmBoth`, for every `O e w₀ cctx` -/
theorem admBoth_mkMetaContext (cctx : Core.Context) :
    AdmBoth O e w₀ Lean.Elab.Command.mkMetaContext cctx :=
  admBoth_none Tools.ShippingStartWorldA.mkMetaContext_canUnfold

theorem AdmBoth.lctx (h : AdmBoth O e w₀ mctx cctx) (l : LocalContext) :
    AdmBoth O e w₀ { mctx with lctx := l } cctx := ⟨admCtx_lctx h.1 l, admCtx_lctx h.2 l⟩

theorem AdmBoth.localInsts (h : AdmBoth O e w₀ mctx cctx) (li : LocalInstances) :
    AdmBoth O e w₀ { mctx with localInstances := li } cctx := ⟨admCtx_localInsts h.1 li, admCtx_localInsts h.2 li⟩

theorem AdmBoth.lctx_insts (h : AdmBoth O e w₀ mctx cctx) (l : LocalContext) (li : LocalInstances) :
    AdmBoth O e w₀ { mctx with lctx := l, localInstances := li } cctx :=
  ⟨admCtx_lctx_insts h.1 l li, admCtx_lctx_insts h.2 l li⟩

theorem AdmBoth.config (h : AdmBoth O e w₀ mctx cctx) (c : ConfigWithKey) :
    AdmBoth O e w₀ { mctx with keyedConfig := c } cctx := ⟨admCtx_config h.1 c, admCtx_config h.2 c⟩

theorem AdmBoth.cctx (h : AdmBoth O e w₀ mctx cctx) (cctx' : Core.Context) :
    AdmBoth O e w₀ mctx cctx' := h

/-- **the only place `AdmDownR` enters**: it turns a context admissible for the strengthened bundle into an `AdmBoth` one (so S2m's `ropsR` is `opsB` + this conversion) -/
theorem admBoth_of_down (hdown : AdmDownR O e w₀) (h : AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx) :
    AdmBoth O e w₀ mctx cctx := ⟨hdown mctx cctx h, h⟩

/-- `AdmBoth` for the strengthened bundle only where it is also admissible for the plain predicate: the plain half of `AdmBoth` is what the fields of `O` need -/
theorem AdmBoth.plain (h : AdmBoth O e w₀ mctx cctx) : AdmCtx O.quiet mctx cctx := h.1

/-! ## the strengthened operations laws on `AdmBoth` contexts (the `ropsR` fields without `hdown`) -/

/-- **The strengthened operations laws, indexed by `AdmBoth` contexts.** The ten fields of `RefLawsAOps` at `quiet := quietR O.quiet mref cref e w₀`, with the context hypothesis `AdmBoth` in place of `AdmCtx quietR`. (A `Prop`: the laws, not a bundle for the S2h chain; see `opsB_toStd`.) -/
structure OpsB (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : Void IO.RealWorld) : Prop where
  diag : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmBoth O e w₀ mctx cctx →
    ∀ (p : MetaM α), Diag p → ∀ w, quietR O.quiet mref cref e w₀ w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quietR O.quiet mref cref e w₀ (endW mctx mref cctx cref p w)
  frameT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmBoth O e w₀ mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, quietR O.quiet mref cref e w₀ w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quietR O.quiet mref cref e w₀ (endW mctx mref cctx cref p w)
  excOk : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmBoth O e w₀ mctx cctx →
    ∀ (p : MetaM α), Tools.ShippingChildInv.Op p →
    ∀ w ex w', quietR O.quiet mref cref e w₀ w → p mctx mref cctx cref w = .error ex w' → Tools.ShippingChildInv.OkExc ex
  frameQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmBoth O e w₀ mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ∀ w, quietR O.quiet mref cref e w₀ w →
    quietR O.quiet mref cref e w₀ (endW mctx mref cctx cref p w)
  cacheSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmBoth O e w₀ mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    quietR O.quiet mref cref e w₀ w → quietR O.quiet mref cref e w₀ w'
  depthSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmBoth O e w₀ mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    quietR O.quiet mref cref e w₀ w → quietR O.quiet mref cref e w₀ w'

variable (hcell : CellPrem MkRefd mref cref)
include hcell

/-- **The strengthened laws without `AdmDownR`**: the same proofs as the fields of S2m's `ropsR`, with the plain half of `AdmBoth` in place of `hdown`. The class-D rows and the diagnostics still use the named hypotheses `hD`, `hG`. -/
theorem opsB (hD : DRowEnvR O e w₀) (hG : DiagEnvR O e w₀) : OpsB O e w₀ where
  diag := by
    intro mctx cctx α adm p hp w hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm.1
    have H := O.diag a p hp w hq
    exact ⟨H.1, H.2, hG mctx cctx p a hp w hq hR hr, .step hr (.diag mctx cctx p w a hp)⟩
  frameT := by
    intro mctx cctx α adm p hp w hw
    obtain ⟨hq, hR, hr⟩ := hw
    obtain ⟨hC, hS, hD', hSide, hFresh, hm, hmf, hmne, hc, hsg⟩ := hcell
    have a := adm.1
    have H := O.frameT a p hp w hq
    exact ⟨H.1, H.2, readsAt_endW (envFrameEnd_throws hp hc hm) hR, .step hr (.throws mctx cctx p w a hp)⟩
  excOk := by
    intro mctx cctx α adm p hp w ex w' hw h
    exact O.excOk adm.1 p hp w ex w' hw.1 h
  frameQ := by
    intro mctx cctx α adm p hp w hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm.1
    refine ⟨O.frameQ a p hp w hq, ?_, hr.leafFrame a hp⟩
    by_cases hnd : DRow p
    · exact hD mctx cctx p a hnd w hq hR hr
    · exact readsAt_endW (envFrameEnd_framedA hcell hp hnd) hR
  cacheSetQ := by
    intro mctx cctx adm v w u w' h hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm.1
    have he := Tools.ShippingChildInv.endW_of_runs h
    have hf : Tools.ShippingGen5EnvFrame.EnvFrameEnd (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref :=
      Tools.ShippingGen5EnvFrame.envFrameEnd_set v hcell.1.2.1 hcell.1.2.2
    refine ⟨O.cacheSetQ a v w u w' h hq, ?_, .step hr (.cacheSet mctx cctx v w u w' a h)⟩
    rw [← he]
    exact readsAt_endW hf hR
  depthSetQ := by
    intro mctx cctx adm v w u w' h hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm.1
    have he := Tools.ShippingChildInv.endW_of_runs h
    have hf : Tools.ShippingGen5EnvFrame.EnvFrameEnd (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref :=
      Tools.ShippingGen5EnvFrame.envFrameEnd_set v hcell.2.2.1.2.1 hcell.2.2.1.2.2
    refine ⟨O.depthSetQ a v w u w' h hq, ?_, .step hr (.depthSet mctx cctx v w u w' a h)⟩
    rw [← he]
    exact readsAt_endW hf hR

end Both

/-! ## (C) the world-level replacement of `AdmDownR` -/

section Cover
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`QuietCover`** (replacement premise, world-level): every world of the laws' quiet predicate reads the root environment `e` and is reached from the root start world `w₀` by leaf steps. A statement about the quiet predicate of the laws, not about callbacks and not about contexts. -/
def QuietCover (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : Void IO.RealWorld) : Prop :=
  ∀ w : Void IO.RealWorld, O.quiet w → ReadsAt e cref w ∧ Reached O.quiet mref cref w₀ w

variable {O : RefLawsAOps MkRefd mref cref} {e : Environment} {w₀ : Void IO.RealWorld}

/-- under the cover the strengthened quiet predicate IS the plain one -/
theorem quietR_eq_of_cover (h : QuietCover O e w₀) : quietR O.quiet mref cref e w₀ = O.quiet :=
  funext fun w => propext ⟨fun h' => h'.1, fun hq => ⟨hq, (h w hq).1, (h w hq).2⟩⟩

/-- `AdmDownR` is a theorem under the cover: the two quiet predicates are equal, so the two admissibilities are the same -/
theorem admDownR_of_cover (h : QuietCover O e w₀) : AdmDownR O e w₀ := by
  intro mctx cctx a
  rw [quietR_eq_of_cover h] at a
  exact a

theorem drow_toFramedA {α : Type} {p : MetaM α} (h : DRow p) : FramedA MkRefd p := by
  cases h with
  | ioEnv n => exact FramedA.ioEnv n
  | monoMs => exact FramedA.monoMs
  | mkExprCache v => exact FramedA.mkExprCache v
  | localMk v hl => exact FramedA.localMk v hl
  | whnf e => exact FramedA.whnf e
  | inferType e => exact FramedA.inferType e
  | isClass? e => exact FramedA.isClass? e
  | whnfUntil e n => exact FramedA.whnfUntil e n
  | instantiateForall e ps => exact FramedA.instantiateForall e ps
  | mkLambdaFVars xs e a b c d bi => exact FramedA.mkLambdaFVars xs e a b c d bi
  | mkAppM c xs => exact FramedA.mkAppM c xs
  | unfoldDefinition? e => exact FramedA.unfoldDefinition? e
  | reduce e a b c => exact FramedA.reduce e a b c

/-- the class-D hypothesis is a theorem under the cover: the plain law `frameQ` keeps quiet, and every quiet world is covered -/
theorem drowEnvR_of_cover (h : QuietCover O e w₀) : DRowEnvR O e w₀ := by
  intro mctx cctx α p a hd w hq _ _
  exact (h _ (O.frameQ a p (drow_toFramedA hd) w hq)).1

/-- the diagnostic hypothesis is a theorem under the cover (the plain law `diag` keeps quiet) -/
theorem diagEnvR_of_cover (h : QuietCover O e w₀) : DiagEnvR O e w₀ := by
  intro mctx cctx α p a hd w hq _ _
  exact (h _ (O.diag a p hd w hq).2).1

/-- the telescope hypothesis is the laws' own `T` under the cover -/
theorem teleR_of_cover (h : QuietCover O e w₀) (T : RefLawsATele O.quiet mref cref) : TeleR O e w₀ := by
  show RefLawsATele (quietR O.quiet mref cref e w₀) mref cref
  rw [quietR_eq_of_cover h]
  exact T

end Cover

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`hftCoreCloses_of_kidsR'`: `hftCoreCloses_of_kidsR` with `hdown : AdmDownR …` REPLACED by `hcover : QuietCover L.O (envAt cref w) w`.** (The other premises `hadm hD hG hT hs h0` are as in S2m; they are theorems under the cover, see `hftCoreCloses_of_cover`.) -/
theorem hftCoreCloses_of_kidsR' (L : Laws mref cref) {w : Void IO.RealWorld}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hcover : QuietCover L.O (envAt cref w) w)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses mctx mref cctx cref w :=
  hftCoreCloses_of_kidsR L hstart hcell hrH hrT hg hadm (admDownR_of_cover hcover) hD hG hT hs h0

/-- **Everything the cover makes redundant, removed**: `hftCoreCloses_of_kidsR` with the seven premises `hadm hdown hD hG hT hs h0` replaced by `hcover hs h0` (`hadm` is `hstart.1`, `hdown hD hG hT` are theorems under the cover). -/
theorem hftCoreCloses_of_cover (L : Laws mref cref) {w : Void IO.RealWorld}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat}
    (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hg : HftKidsGates (envAt cref w))
    (hcover : QuietCover L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w) :
    HftCoreCloses mctx mref cctx cref w := by
  have hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx := by
    rw [quietR_eq_of_cover hcover]
    exact hstart.1
  exact hftCoreCloses_of_kidsR' L hstart hcell hrH hrT hg hadm hcover (drowEnvR_of_cover hcover)
    (diagEnvR_of_cover hcover) (teleR_of_cover hcover L.T) hs h0

end Tools.ShippingFGCircuitS2nAdm

#print axioms Tools.ShippingFGCircuitS2nAdm.opsB
#print axioms Tools.ShippingFGCircuitS2nAdm.hftCoreCloses_of_kidsR'
#print axioms Tools.ShippingFGCircuitS2nAdm.hftCoreCloses_of_cover
