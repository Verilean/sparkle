import Tools.ShippingFGCircuitS1kPkg
import Tools.ShippingFGCircuitS1rCD
import Tools.ShippingFGCircuitS1qHead
set_option autoImplicit false
-- FG circuit pilot S1t: the non-leaf root's final statement on the profile-free entry `synthesizeCombinationalOff`, parameterised by the carrier, with the conclusion stated over the NEW carrier, and its assembly. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §24.

/-! # S1t: `synth_hftPcieOutByte_finalOff`

1. **Carrier-generic source meaning** (`CDRel`, `SourceDenotesMonoV`, `RootArtifactMonoV`, `DeclConnectMonoV`): the conclusion side of `RootArtifactMono` with the old `CD [] d.value` replaced by ANY single-environment derivation relation
   `CV env d.value (MonoTy sh) m` (`cdvOld`, `cdvX`, `cdvY`, `cdvZ`; S1s's future family is one more `CDRel`). With `cdvOld` the definitions ARE the old ones (`Iff.rfl`).
2. **The final statement** `HftFinalStmtOff Ob CV`: the top run is `synthesizeCombinationalOff hftRoot`; `hcell : CellPrem` replaces `hhead`/`hcell`; `hcd : Ob (envAt cref w)`; the core obligations `HftObTopCoreOff`/`HftObNoRawOff` speak about
   the profile-free core run; the conclusion is `PostRunOff` and `RootArtifactMonoV CV`.
3. **The assembly** `synth_hftPcieOutByte_finalOff`: from the named obligations (`hcd`, `hsrc`, `htop`, `hnoraw`, the two child readers) to the conclusion, for every `CV` and every `Ob` that implies the root-value derivation.
   Children stay on `synthesizeChild` (the diagnostic entry): see docs §24.2 for what the statement guarantees and what it does not.
4. **Generic lemmas** about the carrier: embeddings `cdvOld → cdvX → cdvY → cdvZ`, uniqueness of the denoted meaning, monotonicity, observation transport. -/
namespace Tools.ShippingFGCircuitS1tFinal
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD

/-! ## 1. carrier-generic source meaning -/

/-- a single-environment derivation relation for a value expression (no valuation: closed at `[]`) -/
abbrev CDRel : Type := Environment → Lean.Expr → (α : Type) → α → Prop

/-- the S1k carrier (no environment) -/
def cdvOld : CDRel := fun _ e α v => CD [] e α v
/-- the S1m/S1p/S1r carriers, each read in the environment it is given -/
def cdvX : CDRel := fun env e α v => CDX env [] e α v
def cdvY : CDRel := fun env e α v => CDY env [] e α v
def cdvZ : CDRel := fun env e α v => CDZ env [] e α v

/-- `SourceDenotesMono` with the derivation relation `CV` read in `env` (the old one is `cdvOld`) -/
def SourceDenotesMonoV (CV : CDRel) (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : MonoTy sh) : Prop :=
  params = [] ∧ ∃ d : DefinitionVal, env.find? source = some (.defnInfo d) ∧ d.levelParams = [] ∧
    monoShapeOf (.defnInfo d) = some sh ∧ CV env d.value (MonoTy sh) m

/-- `RootArtifactMono` over `CV` -/
def RootArtifactMonoV {ι : Type} (CV : CDRel) (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (sh : SigShape) (mm : MonoTy sh)
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  P X = some p ∧ SourceDenotesMonoV CV env X [] sh mm ∧ ObservationsEqualMono sh mm p ∧
    ∀ raw, Post b raw → ∃ n, HasConcretePackage p n X b raw D

/-- the monomorphic `DeclConnect` over `CV` (the shape comes from `monoShapeOf`, the meaning from `CV` in the start environment, the observation equation as in `DeclConnect`) -/
def DeclConnectMonoV {ι : Type} (CV : CDRel) (env₀ : Environment) (P : Pkgs ι (fun _ => defaultDomain)) (Tgt : Name → Prop) : Prop :=
  ∀ X, Tgt X → ∀ p, P X = some p →
    ∃ (d : DefinitionVal) (sh : SigShape) (mm : MonoTy sh), env₀.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ monoShapeOf (.defnInfo d) = some sh ∧
      ShapeMatchesMono sh p.d p.kD ∧ CV env₀ d.value (MonoTy sh) mm ∧ ∀ i bools bits, monoObs sh mm bools bits = p.src i bools bits

/-- the FG circuit conclusion form over `CV` -/
def FGCircuitConclusionMonoV {ι : Type} (CV : CDRel) (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (params : List (String × Nat))
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  (∃ raw, Post b raw) ∧
  ∀ raw, Post b raw → ∃ (sh : SigShape) (m : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)) (n : Nat),
    P X = some p ∧ SourceDenotesMonoV CV env X params sh m ∧ HasConcretePackage p n X b raw D ∧ ObservationsEqualMono sh m p

/-- the old definitions are the `cdvOld` instances (the generalisation is faithful) -/
theorem sourceDenotesMonoV_old (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : MonoTy sh) :
    SourceDenotesMonoV cdvOld env source params sh m ↔ SourceDenotesMono env source params sh m := Iff.rfl

theorem rootArtifactMonoV_old {ι : Type} (env : Environment) (P : Pkgs ι (fun _ => defaultDomain))
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop) (X : Name) (sh : SigShape) (mm : MonoTy sh)
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) :
    RootArtifactMonoV cdvOld env P Post X sh mm b D p ↔ RootArtifactMono env P Post X sh mm b D p := Iff.rfl

/-- the embeddings of the carriers (the only direction that exists: no `CDZ → CD`) -/
theorem cdvOld_to_X : ∀ env e α v, cdvOld env e α v → cdvX env e α v := fun _ _ _ _ h => cdx_of_cd h
theorem cdvX_to_Y : ∀ env e α v, cdvX env e α v → cdvY env e α v := fun _ _ _ _ h => dx_to_dy h
theorem cdvY_to_Z : ∀ env e α v, cdvY env e α v → cdvZ env e α v := fun _ _ _ _ h => dy_to_dz h
theorem cdvOld_to_Z : ∀ env e α v, cdvOld env e α v → cdvZ env e α v := fun _ _ _ _ h => dx_to_dz (cdx_of_cd h)

/-- each carrier is functional: one derivation target fixes the type and the value (this says the relation is a function; it is NOT the statement that the value is the source's meaning) -/
def CDFunctional (CV : CDRel) : Prop := ∀ env e (α β : Type) (v : α) (w : β), CV env e α v → CV env e β w → α = β ∧ HEq v w
theorem cdvOld_functional : CDFunctional cdvOld := fun _ _ _ _ _ _ h h' => cd_fun h h'
theorem cdvX_functional : CDFunctional cdvX := fun _ _ _ _ _ _ h h' => cdx_fun h h'
theorem cdvY_functional : CDFunctional cdvY := fun _ _ _ _ _ _ h h' => cdy_fun h h'
theorem cdvZ_functional : CDFunctional cdvZ := fun _ _ _ _ _ _ h h' => cdz_fun h h'

section Generic
variable {CV CV' : CDRel}

theorem sourceDenotesMonoV_mono (hCV : ∀ env e α v, CV env e α v → CV' env e α v) {env : Environment} {source : Name} {params : List (String × Nat)}
    {sh : SigShape} {m : MonoTy sh} (h : SourceDenotesMonoV CV env source params sh m) : SourceDenotesMonoV CV' env source params sh m := by
  obtain ⟨hp, d, hd, hl, hs, hv⟩ := h
  exact ⟨hp, d, hd, hl, hs, hCV _ _ _ _ hv⟩

/-- the meaning a declaration denotes is unique, for a functional carrier (the functionality of the relation) -/
theorem sourceDenotesMonoV_unique (hf : CDFunctional CV) {env : Environment} {X : Name} {params : List (String × Nat)} {sh sh' : SigShape}
    {m : MonoTy sh} {m' : MonoTy sh'} (h : SourceDenotesMonoV CV env X params sh m) (h' : SourceDenotesMonoV CV env X params sh' m') : sh = sh' ∧ HEq m m' := by
  obtain ⟨-, d, hd, -, hs, hv⟩ := h
  obtain ⟨-, d', hd', -, hs', hv'⟩ := h'
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  rw [hs] at hs'
  have := Option.some.inj hs'
  subst this
  exact ⟨rfl, (hf _ _ _ _ _ _ hv hv').2⟩

/-- same shape: the same meaning (an equation, not only `HEq`) -/
theorem sourceDenotesMonoV_eq (hf : CDFunctional CV) {env : Environment} {X : Name} {params : List (String × Nat)} {sh : SigShape}
    {m m' : MonoTy sh} (h : SourceDenotesMonoV CV env X params sh m) (h' : SourceDenotesMonoV CV env X params sh m') : m = m' :=
  eq_of_heq (sourceDenotesMonoV_unique hf h h').2

/-- the observation correspondence is carrier-independent: it moves along an equation of meanings -/
theorem observationsEqualMono_congr {ι : Type} {sh : SigShape} {m m' : MonoTy sh} {p : Pkg ι (fun _ => defaultDomain)} (h : m = m')
    (ho : ObservationsEqualMono sh m p) : ObservationsEqualMono sh m' p := by
  subst h; exact ho

/-- two derivations of the same declaration (in possibly different carriers, both functional, the second above the first): the observation correspondence of one gives that of the other -/
theorem observationsEqualMono_of_denotes (hf : CDFunctional CV') (hCV : ∀ env e α v, CV env e α v → CV' env e α v) {ι : Type} {env : Environment} {X : Name}
    {sh : SigShape} {m m' : MonoTy sh} {p : Pkg ι (fun _ => defaultDomain)}
    (h : SourceDenotesMonoV CV env X [] sh m) (h' : SourceDenotesMonoV CV' env X [] sh m') (ho : ObservationsEqualMono sh m p) : ObservationsEqualMono sh m' p :=
  observationsEqualMono_congr (sourceDenotesMonoV_eq hf (sourceDenotesMonoV_mono hCV h) h') ho

theorem rootArtifactMonoV_mono (hCV : ∀ env e α v, CV env e α v → CV' env e α v) {ι : Type} {env : Environment} {P : Pkgs ι (fun _ => defaultDomain)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {X : Name} {sh : SigShape} {mm : MonoTy sh}
    {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {p : Pkg ι (fun _ => defaultDomain)}
    (h : RootArtifactMonoV CV env P Post X sh mm b D p) : RootArtifactMonoV CV' env P Post X sh mm b D p :=
  ⟨h.1, sourceDenotesMonoV_mono hCV h.2.1, h.2.2.1, h.2.2.2⟩

/-- the artifact statement gives the conclusion form (`fgCircuitConclusionMono_of_artifact` over `CV`) -/
theorem fgCircuitConclusionMonoV_of_artifact {ι : Type} {env : Environment} {P : Pkgs ι (fun _ => defaultDomain)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {X : Name} {sh : SigShape} {mm : MonoTy sh}
    {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {p : Pkg ι (fun _ => defaultDomain)}
    (hpost : ∃ raw, Post b raw) (h : RootArtifactMonoV CV env P Post X sh mm b D p) : FGCircuitConclusionMonoV CV env P Post X [] b D := by
  obtain ⟨hP, hS, hO, hT⟩ := h
  refine ⟨hpost, fun raw hraw => ?_⟩
  obtain ⟨n, hn⟩ := hT raw hraw
  exact ⟨sh, mm, p, n, hP, hS, hn, hO⟩

/-- the root artifact gives the `DeclConnect` form at the root alone (the callees are not targets: their connection is not claimed here) -/
theorem declConnectMonoV_of_rootArtifact {ι : Type} {env : Environment} {P : Pkgs ι (fun _ => defaultDomain)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {X : Name} {sh : SigShape} {mm : MonoTy sh}
    {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {p : Pkg ι (fun _ => defaultDomain)}
    (h : RootArtifactMonoV CV env P Post X sh mm b D p) : DeclConnectMonoV CV env P (fun Y => Y = X) := by
  obtain ⟨hP, ⟨-, d, hd, hl, hs, hv⟩, ⟨hsm, hobs⟩, -⟩ := h
  intro Y hY q hq
  subst hY
  rw [hP] at hq
  have := Option.some.inj hq
  subst this
  exact ⟨d, sh, mm, hd, hl, hs, hsm, hv, hobs⟩

/-- `DeclConnectMonoV` is monotone in the carrier -/
theorem declConnectMonoV_mono (hCV : ∀ env e α v, CV env e α v → CV' env e α v) {ι : Type} {env₀ : Environment} {P : Pkgs ι (fun _ => defaultDomain)}
    {Tgt : Name → Prop} (h : DeclConnectMonoV CV env₀ P Tgt) : DeclConnectMonoV CV' env₀ P Tgt := by
  intro X hX p hp
  obtain ⟨d, sh, mm, h1, h2, h3, h4, h5, h6⟩ := h X hX p hp
  exact ⟨d, sh, mm, h1, h2, h3, h4, hCV _ _ _ _ h5, h6⟩

end Generic

/-- the old artifact statement (every leaf root's final, S1q `X_final12`) gives the same statement over the `DZ` carrier in the same environment -/
theorem rootArtifactMono_to_Z {ι : Type} {env : Environment} {P : Pkgs ι (fun _ => defaultDomain)}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {X : Name} {sh : SigShape} {mm : MonoTy sh}
    {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {p : Pkg ι (fun _ => defaultDomain)}
    (h : RootArtifactMono env P Post X sh mm b D p) : RootArtifactMonoV cdvZ env P Post X sh mm b D p :=
  rootArtifactMonoV_mono (CV := cdvOld) cdvOld_to_Z (by exact h)

/-! ## 2. the obligations on the profile-free entry -/

/-- **O-CD (carrier-generic)**: the root's value expression is derived by `CV`, read in the environment `env` -/
def HftObOf (CV : CDRel) (env : Environment) : Prop := CV env hftRootValue (MonoTy shHft) synth_hftPcieOutByte

theorem hftObOf_old : HftObOf cdvOld = fun _ => HftObCD := rfl
theorem hftObOf_Y : HftObOf cdvY = HftObCDY := rfl
theorem hftObOf_Z : HftObOf cdvZ = HftObCDZ := rfl

/-- **O-TOP on the profile-free core run** (`TopShips` at the core design `D₀`; the machine boundary is `MachineDefinesLinkedOff`, the run is `synthesizeCombinationalCoreOff`).
UNPROVED: the children's packages and `ChildShips`/`ResetNk`; the children are synthesized by `synthesizeChild` (the diagnostic entry), so whatever the run does for them is inside this hypothesis, not proved. -/
def HftObTopCoreOff {ι : Type} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  (∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' → ∃ n, TopShips p n hftRoot b raw D₀

/-- **O-NORAW on the profile-free core run** (acyclic hierarchy: no instance below the top names the top). UNPROVED. -/
def HftObNoRawOff (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) : Prop :=
  ∀ (raw : Sparkle.IR.AST.Module) (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 →
    Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D' →
    (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) raw) ∧
    (∀ n, Tools.ShippingGen5DCEntryR.NoRawBelow D₀ raw.name (n + 1) (Sparkle.IR.OptCheck.checkedOptimize b)) ∧
    (∀ mn iname conns, Sparkle.IR.AST.Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name)

/-! ## 3. the statement -/

/-- **`HftFinalStmtOff Ob CV`**: the final statement of the non-leaf root `synth_hftPcieOutByte`.
Top run: `synthesizeCombinationalOff hftRoot` (the guaranteed entry). `hcell : CellPrem` supplies the head (`HeadAtOff`) and `ReadWorld`; there is no `hhead`.
`hcd : Ob (envAt cref w)`: the carrier obligation in the start environment (`Ob` is any of `HftObCDX/Y/Z` or a future family). The conclusion: the package from the table, the source meaning over `CV` (read in the SAME start environment), the observation
correspondence, and `TopShips` for every `raw` of `PostRunOff`. The children's own entry (`synthesizeChild`) is NOT changed and is not mentioned in the type. -/
def HftFinalStmtOff (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w)) (hsrc : HftObSrc (ι := ι) lvl (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-! ## 4. the assembly (the analogue of `synth_hftPcieOutByte_final`, on `Off` and the new carrier) -/

/-- **`synth_hftPcieOutByte_finalOff`**: for every carrier `CV` and every obligation `Ob` that gives the root-value derivation in `CV` (`hOb`), the statement holds. The proof is S1k's assembly with: `HeadAtOff` from `CellPrem`
(S1q), `postEntryOff`, `MachineDefinesLinkedOff`, `PostRunOff`; the only carrier-specific step is `hOb`. -/
theorem synth_hftPcieOutByte_finalOff (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) : HftFinalStmtOff Ob CV := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hSrc hTop hNoRaw
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  have hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1 :=
    fun _ _ _ => machineDefinesLinked_of_reader_headAtOff hhead (Tools.ShippingFGCircuitS1hFrame.getEnvFrame_of_readWorld hcell.2.2.2.2.2.2.2.2.1) hE hRead hgates
  obtain ⟨E, hEnt, hsh, hdat⟩ := hRead
  obtain ⟨g, hg, hgd⟩ := canon_row (lvl := lvl) (env := envAt cref w) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := hRdH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := envAt cref w) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := hRdT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := envAt cref w) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : GenData (Tools.ShippingGen5Acc.dataOfAt lvl) Ec (structEnv (envAt cref w))),
      Tools.ShippingGen5Acc.entry₀ (envAt cref w) c = some Ec ∧ canonGD lvl (envAt cref w) Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := genGP_root_kids (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) hEnt hg hkids
  rw [hgd] at hpd
  have hkD : p.kD = 5 := by rw [hkp, hgd]; exact root_kD
  have hl : EndpointLink synth_hftPcieOutByte.machineData 5 (fun _ bools bits => monoObs shHft synth_hftPcieOutByte bools bits) p :=
    ⟨hpd, hkD, hSrc p hP⟩
  have hpost : ∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw := ⟨raw, D₀, w1, hc, hpe⟩
  refine ⟨hpost, synth_hftPcieOutByte, p, hP, ?_, observationsEqualMono_of_link root_shape hl, ?_⟩
  · obtain ⟨hf, hlv, ht, hv⟩ := hE
    refine ⟨rfl, d, hf, hlv, ?_, ?_⟩
    · show (if d.levelParams.isEmpty = true then monoGo [] d.type else none) = some shHft
      rw [hlv, ht]; simpa using hftRootType_shape
    · rw [hv]; exact hOb _ hCD
  · intro raw' ⟨D₀', w1', hr', hpe'⟩
    obtain ⟨n, hn⟩ := hTop p hP hdRun raw' D₀' w1' hr' hpe'
    obtain ⟨h1, h2, h3⟩ := hNoRaw raw' D₀' w1' hr' hpe'
    exact ⟨n, hdecl, topShips_transport p n hftRoot hpe' (h1 n) (h2 n) h3 hn⟩

/-- the instances: each is the assembly at `Ob := HftObOf CV` (or the named S1p/S1r obligation) -/
theorem synth_hftPcieOutByte_finalOff_of (CV : CDRel) : HftFinalStmtOff (HftObOf CV) CV := synth_hftPcieOutByte_finalOff CV _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOff_Z : HftFinalStmtOff HftObCDZ cdvZ := synth_hftPcieOutByte_finalOff cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOff_Y : HftFinalStmtOff HftObCDY cdvY := synth_hftPcieOutByte_finalOff cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOff_X : HftFinalStmtOff HftObCDX cdvX := synth_hftPcieOutByte_finalOff cdvX _ (fun _ h => h)
/-- the old obligation (no environment) over the old carrier -/
theorem synth_hftPcieOutByte_finalOff_old : HftFinalStmtOff (fun _ => HftObCD) cdvOld := synth_hftPcieOutByte_finalOff cdvOld _ (fun _ h => h)

/-- a stronger carrier is a weaker premise-to-conclusion transfer: the statement over `CV` with obligation `Ob` gives the statement over `CV'` when `CV ⊆ CV'` (the conclusion's source meaning is monotone) -/
theorem hftFinalStmtOff_mono {Ob : Environment → Prop} {CV CV' : CDRel} (hCV : ∀ env e α v, CV env e α v → CV' env e α v)
    (h : HftFinalStmtOff Ob CV) : HftFinalStmtOff Ob CV' := by
  intro ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hcd hsrc htop hnoraw
  obtain ⟨hpost, mm, p, hart⟩ := h L lvl env₀ hstart hr hcell hchk hRdH hRdT hcd hsrc htop hnoraw
  exact ⟨hpost, mm, p, rootArtifactMonoV_mono hCV hart⟩

end Tools.ShippingFGCircuitS1tFinal

#print axioms Tools.ShippingFGCircuitS1tFinal.cdvOld_to_Z
#print axioms Tools.ShippingFGCircuitS1tFinal.cdvZ_functional
#print axioms Tools.ShippingFGCircuitS1tFinal.sourceDenotesMonoV_unique
#print axioms Tools.ShippingFGCircuitS1tFinal.sourceDenotesMonoV_eq
#print axioms Tools.ShippingFGCircuitS1tFinal.observationsEqualMono_of_denotes
#print axioms Tools.ShippingFGCircuitS1tFinal.rootArtifactMonoV_mono
#print axioms Tools.ShippingFGCircuitS1tFinal.rootArtifactMono_to_Z
#print axioms Tools.ShippingFGCircuitS1tFinal.fgCircuitConclusionMonoV_of_artifact
#print axioms Tools.ShippingFGCircuitS1tFinal.declConnectMonoV_of_rootArtifact
#print axioms Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOff
#print axioms Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOff_Z
#print axioms Tools.ShippingFGCircuitS1tFinal.hftFinalStmtOff_mono
