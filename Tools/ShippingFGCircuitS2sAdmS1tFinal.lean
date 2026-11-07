import Tools.ShippingFGCircuitS1tFinal
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmCallsGatePinned
import Tools.ShippingFGCircuitS2sAdmRunLocal
import Tools.ShippingFGCircuitS2sAdmLinked
import Tools.ShippingFGCircuitS2sAdmRunReads
import Tools.ShippingFGCircuitS2sAdmServedRealA
import Tools.ShippingFGCircuitS2sAdmParentRanA
import Tools.ShippingFGCircuitS2sAdmParentTailsA
import Tools.ShippingFGCircuitS2sAdmParentDesignA
import Tools.ShippingFGCircuitS2sAdmS1qLinked
-- FG circuit pilot S2s4: SELECTIVE port of ShippingFGCircuitS1tFinal.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
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

section Generic
variable {CV CV' : CDRel}

end Generic

/-- **`HftFinalStmtOffX Ob CV`**: the final statement of the non-leaf root `synth_hftPcieOutByte`.
Top run: `synthesizeCombinationalOff hftRoot` (the guaranteed entry). `hcell : CellPrem` supplies the head (`HeadAtOff`) and `ReadWorld`; there is no `hhead`.
`hcd : Ob (envAt cref w)`: the carrier obligation in the start environment (`Ob` is any of `HftObCDX/Y/Z` or a future family). The conclusion: the package from the table, the source meaning over `CV` (read in the SAME start environment), the observation
correspondence, and `TopShips` for every `raw` of `PostRunOff`. The children's own entry (`synthesizeChild`) is NOT changed and is not mentioned in the type. -/
def HftFinalStmtOffX (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : StartX L mctx cctx w)
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


/-- **`synth_hftPcieOutByte_finalOffX`**: for every carrier `CV` and every obligation `Ob` that gives the root-value derivation in `CV` (`hOb`), the statement holds. The proof is S1k's assembly with: `HeadAtOff` from `CellPrem`
(S1q), `postEntryOff`, `MachineDefinesLinkedOff`, `PostRunOff`; the only carrier-specific step is `hOb`. -/
theorem synth_hftPcieOutByte_finalOffX (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) : HftFinalStmtOffX Ob CV := by
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
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) Ec (structEnv (envAt cref w))),
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
    exact ⟨n, hdecl, Tools.ShippingFGCircuitS1iChild.topShips_transport p n hftRoot hpe' (h1 n) (h2 n) h3 hn⟩


/-- the instances: each is the assembly at `Ob := HftObOf CV` (or the named S1p/S1r obligation) -/
theorem synth_hftPcieOutByte_finalOff_ofX (CV : CDRel) : HftFinalStmtOffX (HftObOf CV) CV := synth_hftPcieOutByte_finalOffX CV _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOff_ZX : HftFinalStmtOffX HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffX cdvZ _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOff_YX : HftFinalStmtOffX HftObCDY cdvY := synth_hftPcieOutByte_finalOffX cdvY _ (fun _ h => h)

theorem synth_hftPcieOutByte_finalOff_XX : HftFinalStmtOffX HftObCDX cdvX := synth_hftPcieOutByte_finalOffX cdvX _ (fun _ h => h)

/-- the old obligation (no environment) over the old carrier -/
theorem synth_hftPcieOutByte_finalOff_oldX : HftFinalStmtOffX (fun _ => HftObCD) cdvOld := synth_hftPcieOutByte_finalOffX cdvOld _ (fun _ h => h)


/-- a stronger carrier is a weaker premise-to-conclusion transfer: the statement over `CV` with obligation `Ob` gives the statement over `CV'` when `CV ⊆ CV'` (the conclusion's source meaning is monotone) -/
theorem hftFinalStmtOff_monoX {Ob : Environment → Prop} {CV CV' : CDRel} (hCV : ∀ env e α v, CV env e α v → CV' env e α v)
    (h : HftFinalStmtOffX Ob CV) : HftFinalStmtOffX Ob CV' := by
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
#print axioms Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOffX
#print axioms Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOff_ZX
#print axioms Tools.ShippingFGCircuitS1tFinal.hftFinalStmtOff_monoX

