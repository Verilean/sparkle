import Tools.ShippingFGCircuitS3kChain
set_option autoImplicit false
-- FG circuit pilot S3k, unit 2: the final statement v11 = v10 WITHOUT `hcache`.  The start-world hypothesis of the chain is `AdmCtx` (from the checked wrapper's run) plus the JQ-only `hjq` (`hquiet`, `hsynth` and `dv w = 0` from the run); the cache invariant at the start world is not an input anywhere (S3kChain; the head of the depth-0 core gives `JQC 1` after it, `jqc_after_head_of_pilotEntry3`).  v9 and v10 are untouched.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §61.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3kFinal
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildBndCore (cv dv sv)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS2mReach Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingFGCircuitS2yFinal (cdvT)
open Tools.ShippingFGCircuitS3b2Reader (lvl₀)
open Tools.ShippingFGCircuitS3jStart (pilotEntry3 admCtx_of_pilotEntry3 dv_of_pilotEntry3 entry2_of_pilotEntry3 jqc_after_head_of_pilotEntry3)
open Tools.ShippingFGCircuitS3f2Final (pilotReaderOk2)
open Tools.ShippingFGCircuitS3f2Final (HftFinalStmtOffCombined9_k synth_hftPcieOutByte_finalOffCombined9_k)

/-- **the start-world hypotheses of the chain from the residual and the run's checks**: `AdmCtx` (the wrapper's `canUnfold?` check) and `JQ L.O.quiet 0 w` = `quiet w` (`hquiet`), `sv w = some synthesizeChild` (`hsynth`), `dv w = 0` (the wrapper's depth check).  There is NO cache invariant here -/
theorem jq_of_residual {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hr : RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w')
    (hquiet : L.O.quiet w) (hsynth : sv w = some synthesizeChild) :
    AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 0 w :=
  ⟨admCtx_of_pilotEntry3 hr L.O.quiet, hquiet, hsynth, dv_of_pilotEntry3 hr⟩

/-- **v11** (10 binders): v10 WITHOUT `hcache`.  Binders: `L hquiet hsynth hr hcell hD hG hT hs h0` (v10's `L hquiet hsynth hcache hr hcell hD hG hT hs h0` minus `hcache`).  The conclusion, `hr` (a run of the checked wrapper `pilotEntry3`) and every other premise are v10's. -/
def HftFinalStmtOffCombined11 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hquiet : L.O.quiet w) (hsynth : sv w = some synthesizeChild)
    (hr : RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-- **v11 from the copied v9** (`hstart` split): the checked wrapper's run gives the S3f2 entry's run from the same `w` (depth cell `ReadWorld`, `hcell.2.2.1.1`) and `AdmCtx ∧ JQ` from the residual and the checks -/
theorem synth_hftPcieOutByte_finalOffCombined11 : HftFinalStmtOffCombined11 := by
  intro ι mref cref L mctx cctx w w' b D' hquiet hsynth hr hcell hD hG hT hs h0
  obtain ⟨hadm, hjq⟩ := jq_of_residual L hr hquiet hsynth
  exact synth_hftPcieOutByte_finalOffCombined9_k L hadm hjq (entry2_of_pilotEntry3 hcell.2.2.1.1 hr) hcell hD hG hT hs h0

/-- **the post-head cache of v11's run**: from exactly v11's premises (`hquiet`, `hsynth`, `hr`, `hcell`) the world after the core head satisfies `JQC L.O 1` including `CacheInvA L.O (cv w1)` (`jqc_after_head_of_pilotEntry3`, i.e. `L.O.cacheSet`); the start world's cache is not a premise -/
theorem v11_post_head_jqc {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (hquiet : L.O.quiet w) (hsynth : sv w = some synthesizeChild)
    (hr : RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w r w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref) :
    ∃ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 : Void IO.RealWorld),
      RunsTo (coreHeadOff hftRoot) mctx mref cctx cref w s w1 ∧ JQC L.O 1 w1 :=
  jqc_after_head_of_pilotEntry3 L hcell.2.2.1.1 hr hquiet hsynth

end Tools.ShippingFGCircuitS3kFinal

#print axioms Tools.ShippingFGCircuitS3kFinal.jq_of_residual
#print axioms Tools.ShippingFGCircuitS3kFinal.synth_hftPcieOutByte_finalOffCombined11
#print axioms Tools.ShippingFGCircuitS3kFinal.v11_post_head_jqc
