import Tools.ShippingFGCircuitS3kFinal
import Tests.Gen5.FGCircuitPilotCheck50
set_option autoImplicit false
-- FG circuit pilot Check51 (S3k): the complete types of v11 (v10 without `hcache`) and of the copied chain's key lemmas (`hstart` split into `hadm` and a JQ-only `hjq`), each against an independently written expected type and mutants (the cache back as a hypothesis, at another world, as `JQC`, the ordinary / S3f2 entry instead of `pilotEntry3`, ...); the binders v11 = v10 − [hcache]; the vacuity of v11's proof; its independence from the original chain; the axioms.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §61.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck51
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS1kStmt (hftRoot hftHttp hftTlp)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuit Tools.ShippingFGCircuitCover
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.IR.AST
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen2 Tools.ShippingFGCircuitS1kPkg Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitBridge Tools.ShippingFGCircuitRoots Tools.ShippingGen5FG Tools.ShippingGen5DeclConnect Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead Tools.ShippingFGCircuitS1tFinal
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod NmRoot NmHttp NmTlp RootData HttpData TlpData Pre)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck33 (ExpQuiet ExpD ExpG ExpT ExpPS ExpDown ExpProfOff)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)
open Tests.Gen5.FGCircuitPilotCheck43 (CVT)
open Tests.Gen5.FGCircuitPilotCheck44 (NmHttpX)
open Tests.Gen5.FGCircuitPilotCheck46 (binderNames)
open Tools.ShippingFGCircuitS2mReach (ReachedX)
open Tools.ShippingGen5Env (ReadsAt)
open Tests.Gen5.FGCircuitPilotCheck46r (lvlZero lvlSucc chkTrue)
open Tests.Gen5.FGCircuitPilotCheck47 (ExpTXind norm47 normC)
open Tests.Gen5.FGCircuitPilotCheck44 (envX)
open Tools.ShippingFGCircuitS3f2Final (pilotReaderOk2 rootDefB)
open Tools.ShippingFGCircuitS1hGates (entryGatesB)
open Tools.ShippingFGCircuitS3b2Reader (lvl₀ rootReaderB mdBeq)
open Tools.ShippingFGCircuitS3b2Final (pilotReaderOk)
open Tools.ShippingFGCircuitS3f2Exp (rootMD)
open Tools.ShippingMachineAuto (MachineData)



open Tools.ShippingFGCircuitS3jStart (pilotEntry3)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInv (readOf endW Throws)
open Tools.ShippingStRefCorrespondence (ReadWorld getW)
open Tools.ShippingChildCacheA (JQC CacheInvA)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)
open Tests.Gen5.FGCircuitPilotCheck48 (chk9 modOf desOf eX norm48 unfold48)

def eX' : EnvK := eX

/-- the wrapper variants (mutants of the ENTRY): 1 = no start checks (the S3f2 entry); 2 = only the `canUnfold?` check; 3 = only the depth check; 4 = the ordinary Off entry; 5 = the `canUnfold?` check reversed (requires a callback); 6 = the depth check against 1 -/
def wrapCtxOnly (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let ctx ← readThe Meta.Context
  unless ctx.canUnfold?.isNone do
    throwError "x"
  synthesizeCombinationalOffR (chk9 0) X
def wrapDepthOnly (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
open Tests.Gen5.FGCircuitPilotCheck50 (F10 F10_real unfold50 norm50)
open Tools.ShippingFGCircuitS3jStart (pilotEntry3)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingGen2 (LawsX StartX)
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2aClose Tools.ShippingFGCircuitS2dKids
open Tools.ShippingFGCircuitS3f2Final (pilotReaderOk2)
open Tools.ShippingFGCircuitS2yFinal (cdvT)
open Tools.ShippingFGCircuitS3b2Reader (lvl₀)
open Tools.ShippingFGCircuitS1tFinal (RootArtifactMonoV)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitS1qEndpoint (PostRunOff)
open Tools.ShippingFGCircuitS1xNoRaw Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS3cTop

/-! ### the start-world hypotheses of the copied chain, written again.  Knob `k`: 0 = `hadm` and the JQ-only `hjq` (the real statement); 1 = no `hadm`; 2 = no `hjq`; 3 = the original `Start`/`StartX` (the cache invariant inside); 4 = `hadm` and `JQC` (the cache half inside `hjq`); 5 = `hjq` at the END world; 6 = `hjq` at depth 1; 7 = `hadm`, `hjq` AND a separate cache hypothesis (`hcache` put back) -/
noncomputable def StartK {mref : Rf1} {cref : Rf2} (L : Laws mref cref) (mctx : Cx) (cctx : Cc) (w w' : W) (k : Nat) (R : Prop) : Prop :=
  if k == 0 then (AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet 0 w → R)
  else if k == 1 then (JQ L.O.quiet 0 w → R)
  else if k == 2 then (AdmCtx L.O.quiet mctx cctx → R)
  else if k == 3 then (Start L mctx cctx w → R)
  else if k == 4 then (AdmCtx L.O.quiet mctx cctx → JQC L.O 0 w → R)
  else if k == 5 then (AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet 0 w' → R)
  else if k == 6 then (AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet 1 w → R)
  else (AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet 0 w → CacheInvA L.O (cv w) → R)
noncomputable def StartKX {mref : Rf1} {cref : Rf2} (L : LawsX mref cref) (mctx : Cx) (cctx : Cc) (w w' : W) (k : Nat) (R : Prop) : Prop :=
  if k == 0 then (L.O.adm mctx cctx → JQ L.O.quiet 0 w → R)
  else if k == 1 then (JQ L.O.quiet 0 w → R)
  else if k == 2 then (L.O.adm mctx cctx → R)
  else if k == 3 then (StartX L mctx cctx w → R)
  else if k == 4 then (L.O.adm mctx cctx → JQCX L.O 0 w → R)
  else if k == 5 then (L.O.adm mctx cctx → JQ L.O.quiet 0 w' → R)
  else if k == 6 then (L.O.adm mctx cctx → JQ L.O.quiet 1 w → R)
  else (L.O.adm mctx cctx → JQ L.O.quiet 0 w → CacheInvAX L.O (cv w) → R)

/-- v9's statement with its start hypothesis as the knob (`k = 3` is the original v9) -/
noncomputable def ExpV9k (k : Nat) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2} (L : Laws mref cref) {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    StartK L mctx cctx w w' k (
    RunsTo (synthesizeCombinationalOffR pilotReaderOk2 hftRoot) mctx mref cctx cref w (b, D') w' →
    CellPrem MkRefd mref cref →
    DRowEnvR L.O (envAt cref w) w → DiagEnvR L.O (envAt cref w) w → TeleRX L.toX.O (envAt cref w) w → ProfStepR L.O w → ProfOffW mref cref w →
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p)

/-- v7's statement (`env₀`, `hchk`, the readers) with its start hypothesis as the knob -/
noncomputable def ExpV7k (k : Nat) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    StartK L mctx cctx w w' k (
    RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w' →
    CellPrem MkRefd mref cref →
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData →
    DRowEnvR L.O (envAt cref w) w → DiagEnvR L.O (envAt cref w) w → TeleRX L.toX.O (envAt cref w) w → ProfStepR L.O w → ProfOffW mref cref w →
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p)

/-- the `LawsX` final statement `HftFinalStmtOffLNLX`, with its start hypothesis as the knob -/
noncomputable def ExpLNLXk (k : Nat) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : Rf1} {cref : Rf2} (L : LawsX mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    StartKX L mctx cctx w w' k (
    RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w' →
    CellPrem MkRefd mref cref →
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData →
    Tools.ShippingFGCircuitS2oOb.HftObCDT (envAt cref w) →
    (∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p) →
    HftCoreCloses mctx mref cctx cref w →
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV cdvT (envAt cref w) (GPt (ι := ι) lvl (envAt cref w)) (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p)

noncomputable def R1 {mref : Rf1} {cref : Rf2} (L : LawsX mref cref) (mctx : Cx) (cctx : Cc) (w : W) : Prop :=
  ∀ (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData →
    HftKidsGates (envAt cref w) → L.O.adm mctx cctx →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w → ProfStepRX L.O w → ProfOffW mref cref w →
    HftCoreCloses mctx mref cctx cref w

/-- `coreOff_ranAX`'s statement -/
noncomputable def ExpRanAXk (k : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {declName : Name} {shape : Tools.ShippingMachineClose.MachineShape} {w w' : W}
    {m : Mod} {d : Design},
    StartKX L mctx cctx w w' k (
    RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w' →
    MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w' →
    CoreCloses declName shape mctx mref cctx cref w →
    Tools.ShippingParentRanA.MachineRanAX L.O mctx cctx declName shape m d)

/-- `hftCoreCloses_of_kidsR''`'s statement (its own `hadm` and `hjq`; the knob changes the pair) -/
noncomputable def ExpKidsR2k (k : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    StartKX L mctx cctx w w k (∀ (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat},
    RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData →
    HftKidsGates (envAt cref w) →
    DRowEnvRX L.O (envAt cref w) w → DiagEnvRX L.O (envAt cref w) w → TeleRX L.O (envAt cref w) w → ProfStepRX L.O w → ProfOffW mref cref w →
    HftCoreCloses mctx mref cctx cref w)

/-- `hftCoreCloses_of_kidsRX`'s statement: the JQ-only `hjq` (knob 0); 1 = none; 2 = `JQCX`; 3 = the original `StartX` -/
noncomputable def ExpKidsRXk (k : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W},
    (if k == 0 then (JQ L.O.quiet 0 w → R1 L mctx cctx w) else if k == 1 then R1 L mctx cctx w else if k == 2 then (JQCX L.O 0 w → R1 L mctx cctx w)
     else if k == 3 then (StartX L mctx cctx w → R1 L mctx cctx w) else (JQ L.O.quiet 1 w → R1 L mctx cctx w))

/-- `hftTop_of_runRX`'s statement -/
noncomputable def ExpTopk (k : Nat) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w : W} {b : Mod} {D' : Design},
    StartK L mctx cctx w w k (
    CellPrem MkRefd mref cref →
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData →
    HftKidsGateFacts (envAt cref w) →
    DRowEnvRX L.toX.O (envAt cref w) w → DiagEnvRX L.toX.O (envAt cref w) w → TeleRX L.toX.O (envAt cref w) w → ProfStepRX L.toX.O w → ProfOffW mref cref w →
    ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)

/-- `hftObNoRawOff_of_localX`'s statement -/
noncomputable def ExpNoRawk (k : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : LawsX mref cref) {w : W} {b : Mod} {D' : Design},
    StartKX L mctx cctx w w k (
    (∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1) →
    HftCoreCloses mctx mref cctx cref w →
    HftObNoRawOff mctx mref cctx cref w b D')

/-- the argument of the copied chain: from the residual and the run's checks -/
noncomputable def ExpJqRes (needQ needS : Bool) (concl : Nat) : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} (L : Laws mref cref) {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w' →
    (if needQ then (L.O.quiet w → (if needS then (sv w = some synthesizeChild → (if concl == 0 then (AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 0 w) else if concl == 1 then (AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w) else if concl == 2 then JQ L.O.quiet 0 w else if concl == 3 then (AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 1 w) else if concl == 4 then (AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 0 w') else if concl == 5 then (AdmCtx L.O.quiet mctx cctx ∧ L.O.quiet w ∧ sv w = some synthesizeChild) else Start L mctx cctx w)) else (if concl == 0 then (AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 0 w) else True))) else
      (if needS then (sv w = some synthesizeChild → (if concl == 0 then (AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 0 w) else True)) else (if concl == 0 then (AdmCtx L.O.quiet mctx cctx ∧ JQ L.O.quiet 0 w) else True)))
noncomputable def ExpJqRes_real : Prop := ExpJqRes true true 0
noncomputable def ExpJqResMu_noQuiet : Prop := ExpJqRes false true 0
noncomputable def ExpJqResMu_noSynth : Prop := ExpJqRes true false 0
noncomputable def ExpJqResMu_jqc : Prop := ExpJqRes true true 1
noncomputable def ExpJqResMu_noAdm : Prop := ExpJqRes true true 2
noncomputable def ExpJqResMu_depth1 : Prop := ExpJqRes true true 3
noncomputable def ExpJqResMu_endWorld : Prop := ExpJqRes true true 4
noncomputable def ExpJqResMu_noDv : Prop := ExpJqRes true true 5
noncomputable def ExpJqResMu_start : Prop := ExpJqRes true true 6

/-- the cache after the core head, from v11's own premises (no start-cache premise); knobs: depth, premises, the world, an added start-cache premise -/
noncomputable def ExpPostHead (D : Nat) (needQ needS needCell : Bool) (atStart addC : Bool) : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} (L : Laws mref cref) {mctx : Cx} {cctx : Cc} {w w' : W} {r : Mod × Design},
    (if needQ then L.O.quiet w else True) → (if needS then sv w = some synthesizeChild else True) →
    RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w r w' →
    (if needCell then CellPrem MkRefd mref cref else True) →
    (if addC then CacheInvA L.O (cv w) else True) →
    ∃ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 : W),
      RunsTo (coreHeadOff hftRoot) mctx mref cctx cref w s w1 ∧ JQC L.O D (if atStart then w else w1)
noncomputable def ExpPostHead_real : Prop := ExpPostHead 1 true true true false false
noncomputable def ExpPostHeadMu_depth0 : Prop := ExpPostHead 0 true true true false false
noncomputable def ExpPostHeadMu_depth2 : Prop := ExpPostHead 2 true true true false false
noncomputable def ExpPostHeadMu_noQuiet : Prop := ExpPostHead 1 false true true false false
noncomputable def ExpPostHeadMu_noSynth : Prop := ExpPostHead 1 true false true false false
noncomputable def ExpPostHeadMu_noCell : Prop := ExpPostHead 1 true true false false false
noncomputable def ExpPostHeadMu_atStart : Prop := ExpPostHead 1 true true true true false
noncomputable def ExpPostHeadMu_cacheBack : Prop := ExpPostHead 1 true true true false true

/-- v11's mutants: v10's statement `F10` (Check50's independently written family) with `hcache` omitted (`nC := false`) is v11; every mutant changes one thing of that.  `F10 (nC := true)` is v10 itself (hcache put back); `ck` places it at another world. -/
noncomputable def F11_real : Prop := F10 (nC := false)
noncomputable def F11Mu_cacheBack : Prop := F10
noncomputable def F11Mu_cacheOther : Prop := F10 (ck := 1)
noncomputable def F11Mu_cacheEmpty : Prop := F10 (ck := 2)
noncomputable def F11Mu_cacheEnd : Prop := F10 (ck := 3)
noncomputable def F11Mu_noQuiet : Prop := F10 (nC := false) (nQ := false)
noncomputable def F11Mu_noSynth : Prop := F10 (nC := false) (nS := false)
noncomputable def F11Mu_noRun : Prop := F10 (nC := false) (nRun := false)
noncomputable def F11Mu_noCell : Prop := F10 (nC := false) (nCell := false)
noncomputable def F11Mu_noD : Prop := F10 (nC := false) (nD := false)
noncomputable def F11Mu_noG : Prop := F10 (nC := false) (nG := false)
noncomputable def F11Mu_noT : Prop := F10 (nC := false) (nT := false)
noncomputable def F11Mu_noPS : Prop := F10 (nC := false) (nPS := false)
noncomputable def F11Mu_noProf : Prop := F10 (nC := false) (nProf := false)
noncomputable def F11Mu_entS3f2 : Prop := F10 (nC := false) (ent := 1)
noncomputable def F11Mu_entCtxOnly : Prop := F10 (nC := false) (ent := 2)
noncomputable def F11Mu_entDepthOnly : Prop := F10 (nC := false) (ent := 3)
noncomputable def F11Mu_entOff : Prop := F10 (nC := false) (ent := 4)
noncomputable def F11Mu_entCtxSome : Prop := F10 (nC := false) (ent := 5)
noncomputable def F11Mu_entDepthOne : Prop := F10 (nC := false) (ent := 6)
noncomputable def F11Mu_root : Prop := F10 (nC := false) (root := NmHttpX)
noncomputable def F11Mu_postRoot : Prop := F10 (nC := false) (postRoot := NmHttpX)
noncomputable def F11Mu_runCtx : Prop := F10 (nC := false) (rk := 1)
noncomputable def F11Mu_runWorld : Prop := F10 (nC := false) (rk := 2)
noncomputable def F11Mu_quietOther : Prop := F10 (nC := false) (qk := 1)
noncomputable def F11Mu_quietAll : Prop := F10 (nC := false) (qk := 2)
noncomputable def F11Mu_quietEnd : Prop := F10 (nC := false) (qk := 3)
noncomputable def F11Mu_synthOther : Prop := F10 (nC := false) (sk := 1)
noncomputable def F11Mu_synthNone : Prop := F10 (nC := false) (sk := 2)
noncomputable def F11Mu_synthEnd : Prop := F10 (nC := false) (sk := 3)
noncomputable def F11Mu_addAdm : Prop := F10 (nC := false) (addAdm := true)
noncomputable def F11Mu_addDv : Prop := F10 (nC := false) (addDv := true)
noncomputable def F11Mu_addBoth : Prop := F10 (nC := false) (addAdm := true) (addDv := true)
noncomputable def F11Mu_addStart : Prop := F10 (nC := false) (addStart := true)
noncomputable def F11Mu_reachEnd : Prop := F10 (nC := false) (eA := eE)
noncomputable def F11Mu_reachOther : Prop := F10 (nC := false) (eA := eX)
noncomputable def F11Mu_conEnd : Prop := F10 (nC := false) (conE := eE)
noncomputable def F11Mu_conOther : Prop := F10 (nC := false) (conE := eX)
noncomputable def F11Mu_teleV6 : Prop := F10 (nC := false) (tele := 1)
noncomputable def F11Mu_teleOrigPlain : Prop := F10 (nC := false) (tele := 2)
noncomputable def F11Mu_teleOrigX : Prop := F10 (nC := false) (tele := 3)
noncomputable def F11Mu_teleAdmStrong : Prop := F10 (nC := false) (tele := 4)
noncomputable def F11Mu_lvlGPt0 : Prop := F10 (nC := false) (lvG := lvlZero)
noncomputable def F11Mu_lvlGPtSucc : Prop := F10 (nC := false) (lvG := lvlSucc)
noncomputable def F11Mu_outModule : Prop := F10 (nC := false) (outM := 1)
noncomputable def F11Mu_outDesign : Prop := F10 (nC := false) (outM := 2)
noncomputable def F11Mu_artHttp : Prop := F10 (nC := false) (art := NmHttp)
noncomputable def F11Mu_noC1 : Prop := F10 (nC := false) (c1 := false)
noncomputable def F11Mu_noC2 : Prop := F10 (nC := false) (c2 := false)
noncomputable def F11Mu_carrierZ : Prop := F10 (nC := false) (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)

def unfold51 : List Name := unfold50 ++ [``Tools.ShippingFGCircuitS3kFinal.HftFinalStmtOffCombined11,
  ``Tools.ShippingFGCircuitS3f2Final.HftFinalStmtOffCombined9_k, ``Tools.ShippingFGCircuitS3cFinal.HftFinalStmtOffCombined7_k,
  ``Tools.ShippingFGCircuitS1zClose.HftFinalStmtOffLNLX_k, ``Tools.ShippingFGCircuitS1zClose.HftFinalStmtOffLNLX,
  ``Tools.ShippingFGCircuitS3cFinal.HftFinalStmtOffCombined7, ``Tools.ShippingFGCircuitS1tFinal.cdvT]
def norm51 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold51.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm50 e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck51 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- (A) the complete type of v11
  let f11ty ← tyOf ``Tools.ShippingFGCircuitS3kFinal.synth_hftPcieOutByte_finalOffCombined11
  let f11 ← norm51 f11ty
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined11" f11 (← norm51 (Q "F11_real"))
  Tests.Gen5.FGCircuitCmp.checkSame "HftFinalStmtOffCombined11 = the theorem's type" f11 (← norm51 (Lean.mkConst ``Tools.ShippingFGCircuitS3kFinal.HftFinalStmtOffCombined11))
  for mu in ["F11Mu_cacheBack", "F11Mu_cacheOther", "F11Mu_cacheEmpty", "F11Mu_cacheEnd", "F11Mu_noQuiet", "F11Mu_noSynth", "F11Mu_noRun", "F11Mu_noCell", "F11Mu_noD", "F11Mu_noG", "F11Mu_noT", "F11Mu_noPS", "F11Mu_noProf",
      "F11Mu_entS3f2", "F11Mu_entCtxOnly", "F11Mu_entDepthOnly", "F11Mu_entOff", "F11Mu_entCtxSome", "F11Mu_entDepthOne", "F11Mu_root", "F11Mu_postRoot", "F11Mu_runCtx", "F11Mu_runWorld",
      "F11Mu_quietOther", "F11Mu_quietAll", "F11Mu_quietEnd", "F11Mu_synthOther", "F11Mu_synthNone", "F11Mu_synthEnd",
      "F11Mu_addAdm", "F11Mu_addDv", "F11Mu_addBoth", "F11Mu_addStart", "F11Mu_reachEnd", "F11Mu_reachOther", "F11Mu_conEnd", "F11Mu_conOther",
      "F11Mu_teleV6", "F11Mu_teleOrigPlain", "F11Mu_teleOrigX", "F11Mu_teleAdmStrong", "F11Mu_lvlGPt0", "F11Mu_lvlGPtSucc", "F11Mu_outModule", "F11Mu_outDesign", "F11Mu_artHttp",
      "F11Mu_noC1", "F11Mu_noC2", "F11Mu_carrierZ"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined11 vs {mu}" f11 (← norm51 (Q mu)); nm := nm + 1
  for (what, c) in [("v10", ``Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10), ("v9", ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9),
      ("the copied v9", ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9_k), ("v8", ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8),
      ("v7", ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7)] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined11 vs the {what} theorem's type" f11 (← norm51 (← tyOf c)); nm := nm + 1
  -- (B) the chain's key lemmas: the real statement with the knob = 0, mutants = the other knobs; knob 3 is the ORIGINAL statement
  let mut nmL : Nat := 0
  -- the knob-3 statements are the original types: Exp..k 3 = the original theorem's type
  Tests.Gen5.FGCircuitCmp.checkSame "Exp ≡ original v9 (knob 3)" (← norm51 (← tyOf ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9)) (← norm51 (Lean.mkApp (Q "ExpV9k") (toExpr (3 : Nat))))
  let lemmasK : List (Name × String × List Nat) := [
    (``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9_k, "ExpV9k", [1, 2, 3, 4, 5, 6, 7]),
    (``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7_k, "ExpV7k", [1, 2, 3, 4, 5, 6, 7]),
    (``Tools.ShippingFGCircuitS1zClose.synth_hftPcieOutByte_finalOffLNLX_k, "ExpLNLXk", [1, 2, 3, 4, 5, 6, 7]),
    (``Tools.ShippingFGCircuitS1zClose.coreOff_ranAX_k, "ExpRanAXk", [1, 2, 3, 4, 5, 6, 7]),
    (``Tools.ShippingFGCircuitS1zClose.hftObNoRawOff_of_localX_k, "ExpNoRawk", [1, 2, 3, 4, 5, 6, 7]),
    (``Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR''_k, "ExpKidsR2k", [1, 2, 3, 4, 6, 7]),
    (``Tools.ShippingFGCircuitS3cTop.hftTop_of_runRX_k, "ExpTopk", [1, 2, 3, 4, 6, 7]),
    (``Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsRX_k, "ExpKidsRXk", [1, 2, 3, 4])]
  for (n, ex, ks) in lemmasK do
    let t ← norm51 (← tyOf n)
    Tests.Gen5.FGCircuitCmp.checkSame s!"{n}" t (← norm51 (Lean.mkApp (Q ex) (toExpr (0 : Nat))))
    for k in ks do
      Tests.Gen5.FGCircuitCmp.checkDiff s!"{n} vs {ex} {k}" t (← norm51 (Lean.mkApp (Q ex) (toExpr k))); nmL := nmL + 1
  let lemmasR : List (Name × String × List String) := [
    (``Tools.ShippingFGCircuitS3kFinal.jq_of_residual, "ExpJqRes_real", ["ExpJqResMu_noQuiet", "ExpJqResMu_noSynth", "ExpJqResMu_jqc", "ExpJqResMu_noAdm", "ExpJqResMu_depth1", "ExpJqResMu_endWorld", "ExpJqResMu_noDv", "ExpJqResMu_start"]),
    (``Tools.ShippingFGCircuitS3kFinal.v11_post_head_jqc, "ExpPostHead_real", ["ExpPostHeadMu_depth0", "ExpPostHeadMu_depth2", "ExpPostHeadMu_noQuiet", "ExpPostHeadMu_noSynth", "ExpPostHeadMu_noCell", "ExpPostHeadMu_atStart", "ExpPostHeadMu_cacheBack"])]
  for (n, real, mus) in lemmasR do
    let t ← norm51 (← tyOf n)
    Tests.Gen5.FGCircuitCmp.checkSame s!"{n}" t (← norm51 (Q real))
    for mu in mus do
      Tests.Gen5.FGCircuitCmp.checkDiff s!"{n} vs {mu}" t (← norm51 (Q mu)); nmL := nmL + 1
  logInfo m!"FGCIRCUIT51 SIGNATURES: the complete type of synth_hftPcieOutByte_finalOffCombined11 equals the independently written F11_real (Check50's F10 family with the cache premise omitted) under ONE criterion (FGCircuitCmp.stmtEq after the ONE normalisation function norm51); {nm} mutants rejected (hcache put back at the start world / another world / an empty cache / the end world, each premise dropped, the S3f2 / ordinary / half-checked / depth-1 entry instead of pilotEntry3, another run context or start world, the start conjuncts or the whole Start as hypotheses, the conclusion's environment / tele / level / output / artifact / carrier, and the v10 / v9 / copied-v9 / v8 / v7 types); the copied chain's key lemmas ({lemmasK.length + lemmasR.length}) equal their independently written statements (knob 0; knob 3 of the v9 statement equals the ORIGINAL v9 type), {nmL} mutants rejected (no hadm, no hjq, the original Start/StartX, the cache back inside hjq as JQC/JQCX, hjq at the end world or depth 1, hjq plus a separate cache hypothesis)"
  -- (C) BINDERS: v11 = v10 - [hcache]; field level
  let bl (t : Lean.Expr) : MetaM (List Name) := do return binderNames ((← unfoldDefinition? t).getD t)
  let f10ty ← tyOf ``Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10
  let f9ty ← tyOf ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9
  let b9 ← bl f9ty
  let b10 ← bl f10ty
  let b11 ← bl f11ty
  unless b10 == [`ι, `mref, `cref, `L, `mctx, `cctx, `w, `w', `b, `D', `hquiet, `hsynth, `hcache, `hr, `hcell, `hD, `hG, `hT, `hs, `h0] do throwError "v10 binders: {b10}"
  unless b11 == [`ι, `mref, `cref, `L, `mctx, `cctx, `w, `w', `b, `D', `hquiet, `hsynth, `hr, `hcell, `hD, `hG, `hT, `hs, `h0] do throwError "v11 binders: {b11}"
  unless b11 == b10.filter (· != `hcache) do throwError "v11 is not v10 minus hcache"
  unless b11.length - 9 == 10 do throwError "v11 does not have 10 hypotheses binders"
  -- field level: Start's five conjuncts at v11's own variables: each is a v11 hypothesis, supplied by the run, or absent (no longer a premise)
  let conjuncts ← Meta.forallTelescope ((← unfoldDefinition? f11ty).getD f11ty) fun xs _ => do
    let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName)
    let find (n : Name) : MetaM Lean.Expr := do
      let some i := names.findIdx? (· == n) | throwError "no binder {n}"
      pure xs[i]!
    let st ← mkAppM ``Tools.ShippingGen2.Start #[← find `L, ← find `mctx, ← find `cctx, ← find `w]
    let st ← whnfD st
    let some (adm, jqc) := st.and? | throwError "Start is not a conjunction: {st}"
    let jqc ← whnfD jqc
    let some (jq, cache) := jqc.and? | throwError "JQC is not a conjunction"
    let jq ← whnfD jq
    let some (qu, rest) := jq.and? | throwError "JQ is not a conjunction"
    let some (sy, dd) := rest.and? | throwError "JQ rest is not a conjunction"
    let hyps ← [`hquiet, `hsynth].mapM fun n => do inferType (← find n)
    let cs : List (String × Lean.Expr) := [("AdmCtx", adm), ("quiet w", qu), ("sv w = some synthesizeChild", sy), ("dv w = 0", dd), ("CacheInvA (cv w)", cache)]
    let mut gone : List String := []
    let mut kept : List String := []
    for (nm, c) in cs do
      let mut found := false
      for h in hyps do
        if ← isDefEq h c then found := true
      if found then kept := kept ++ [nm] else gone := gone ++ [nm]
    pure (kept, gone)
  unless conjuncts.1 == ["quiet w", "sv w = some synthesizeChild"] && conjuncts.2 == ["AdmCtx", "dv w = 0", "CacheInvA (cv w)"] do
    throwError "field-level Start comparison: kept {conjuncts.1}, not a v11 hypothesis {conjuncts.2}"
  logInfo m!"FGCIRCUIT51 BINDERS (9 implicit + explicit): v9 ({b9.length} = 9 + 9) {b9}; v10 ({b10.length} = 9 + 11) {b10}; v11 ({b11.length} = 9 + 10) {b11}; v11 = v10 − [hcache]; Start's five conjuncts at v11's own variables: v11 hypotheses {conjuncts.1}; supplied by the run's checks (AdmCtx, dv w = 0) and no longer a premise (CacheInvA (cv w)) {conjuncts.2}"

/-! ## (D) the vacuous `L` is not reached; v11's proof goes through the copies, not the originals -/
run_cmd liftTermElabM do
  let env ← getEnv
  let bad : List Name := [``Tools.ShippingFGCircuitS3jFinal.vacuousLaws, ``Tools.ShippingChildInvA.RefLawsAOps.quietFalse, ``Tools.ShippingChildInvA.RefLawsATele.quietFalse,
    ``Tools.ShippingChildInvA.admCtx_quietFalse, ``Tools.ShippingChildInvA.admCtx_quietFalse_writer, ``Tools.ShippingChildInvA.frame_quietFalse_vacuous]
  -- the original chain's declarations that consume Start / StartX at the start world: none may be reached
  let origs : List Name := [``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9, ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7,
    ``Tools.ShippingFGCircuitS3cTop.hftTop_of_runRX, ``Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR'', ``Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsRX,
    ``Tools.ShippingFGCircuitS1zClose.synth_hftPcieOutByte_finalOffLNLX, ``Tools.ShippingFGCircuitS1zClose.coreOff_ranAX, ``Tools.ShippingFGCircuitS1zClose.hftPostGate_of_localX,
    ``Tools.ShippingFGCircuitS1zClose.hftObNoRawOff_of_localX, ``Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffLX, ``Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOffX,
    ``Tools.ShippingFGCircuitS3cTop.jqc_toX, ``Tools.ShippingFGCircuitS3jFinal.start_of_residual, ``Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10]
  let mut seen : NameSet := {}
  let mut todo : List Name := [``Tools.ShippingFGCircuitS3kFinal.synth_hftPcieOutByte_finalOffCombined11]
  let mut hit : List Name := []
  let mut hitO : List Name := []
  let mut fuel := 200000
  while !todo.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if bad.contains n then hit := n :: hit
      if origs.contains n then hitO := n :: hitO
      if let some ci := env.find? n then
        for c in ci.getUsedConstantsAsSet.toList do
          unless seen.contains c do todo := c :: todo
  unless fuel > 0 do throwError "the dependency walk ran out of fuel"
  unless hit.isEmpty do throwError "FGCIRCUIT51 VACUITY: v11's proof reaches {hit}"
  unless hitO.isEmpty do throwError "FGCIRCUIT51 INDEPENDENCE: v11's proof reaches the original chain {hitO}"
  logInfo m!"FGCIRCUIT51 VACUITY: v11's proof reaches {seen.size} constants and none of vacuousLaws / RefLawsAOps.quietFalse / RefLawsATele.quietFalse / admCtx_quietFalse(_writer) / frame_quietFalse_vacuous, so it does not reach the vacuous L (quiet := False); v11 binds hquiet : L.O.quiet w (false at every world of the vacuous L, S3j vacuous_no_hquiet), and the check's AdmCtx is true at quiet := False (S3j vacuous_adm_trivial) — it is not a witness.  INDEPENDENCE: the same walk reaches none of the {origs.length} original declarations (v9, v7, hftTop_of_runRX, the kids closings, LNLX, coreOff_ranAX, hftPostGate/hftObNoRaw, LX, X, jqc_toX, start_of_residual, v10): the proof goes through the copies only"

/-! ## (E) AXIOMS -/
run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS1tFinal.synth_hftPcieOutByte_finalOffX_k, ``Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffLX_k,
    ``Tools.ShippingFGCircuitS1zClose.coreOff_ranAX_k, ``Tools.ShippingFGCircuitS1zClose.hftPostGate_of_localX_k, ``Tools.ShippingFGCircuitS1zClose.hftObNoRawOff_of_localX_k,
    ``Tools.ShippingFGCircuitS1zClose.synth_hftPcieOutByte_finalOffLNLX_k, ``Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsRX_k, ``Tools.ShippingFGCircuitS2sAdmS2nAdm.hftCoreCloses_of_kidsR''_k,
    ``Tools.ShippingFGCircuitS3cTop.hftTop_of_runRX_k, ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7_k, ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9_k,
    ``Tools.ShippingFGCircuitS3kFinal.jq_of_residual, ``Tools.ShippingFGCircuitS3kFinal.synth_hftPcieOutByte_finalOffCombined11, ``Tools.ShippingFGCircuitS3kFinal.v11_post_head_jqc]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT51 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck51
