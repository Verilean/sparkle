import Tools.ShippingFGCircuitS3jFinal
import Tools.ShippingFGCircuitS3jThrows
import Tests.Gen5.FGCircuitPilotCheck48
set_option autoImplicit false
-- FG circuit pilot Check50 (S3j): the complete types of the new lemmas (the wrapper's run lemma, AdmCtx / dv from the run, the entry-2 run from the same world, the two refusals, the cache half after the core head, the Start assembly, frameT for Throws) and of v10 (11 binders) against independently written expected types under ONE normalisation path (FGCircuitCmp.stmtEq), mutants; the field-level BINDERS of v10 against `Start`; negative controls (another Meta context, depth not 0, another start world, a non-empty cache, the vacuous L); the output of the new entry; AXIOMS.  docs/FG-CIRCUIT-PILOT.md §60.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck50
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
  let depth ← sparkleSynthDepth.get
  unless depth == 0 do
    throwError "x"
  synthesizeCombinationalOffR (chk9 0) X
def wrapCtxSome (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let ctx ← readThe Meta.Context
  unless ctx.canUnfold?.isSome do
    throwError "x"
  let depth ← sparkleSynthDepth.get
  unless depth == 0 do
    throwError "x"
  synthesizeCombinationalOffR (chk9 0) X
def wrapDepthOne (X : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let ctx ← readThe Meta.Context
  unless ctx.canUnfold?.isNone do
    throwError "x"
  let depth ← sparkleSynthDepth.get
  unless depth == 1 do
    throwError "x"
  synthesizeCombinationalOffR (chk9 0) X

/-- **v10, written again** (the 11 binders `L hquiet hsynth hcache hr hcell hD hG hT hs h0`).  Knobs: the premises (Bool); `ent` the run's entry (0 = `pilotEntry3`, 1-6 the variants above); `rk` the run's start (0 = `w`, 1 = another Meta context `mctx2`, 2 = another start world `w2`); `qk` / `sk` / `ck` the three residual premises (0 = real, 1 = at another world, 2 = another form, 3 = at the END world); `addAdm` / `addDv` / `addStart`: the conjuncts the checks supply (or the whole `Start`) as hypotheses AGAIN; the conclusion as in Check48. -/
noncomputable def Exp10 (nQ nS nC nRun nCell nD nG nT nPS nProf : Bool) (ent rk qk sk ck tele : Nat) (addAdm addDv addStart : Bool)
    (lvG : Lean.Expr → Nat) (c1 c2 : Bool) (eA conE : EnvK) (root postRoot art : Name) (outM : Nat) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Pre nQ (if qk == 0 then L.O.quiet w else if qk == 1 then (∃ w2 : W, L.O.quiet w2) else if qk == 2 then (∀ w2 : W, L.O.quiet w2) else L.O.quiet w') (
    Pre nS (if sk == 0 then sv w = some synthesizeChild else if sk == 1 then (∃ w2 : W, sv w2 = some synthesizeChild) else if sk == 2 then sv w = none else sv w' = some synthesizeChild) (
    Pre nC (if ck == 0 then CacheInvA L.O (cv w) else if ck == 1 then (∃ w2 : W, CacheInvA L.O (cv w2)) else if ck == 2 then cv w = {} else CacheInvA L.O (cv w')) (
    Pre addAdm (AdmCtx L.O.quiet mctx cctx) (
    Pre addDv (dv w = 0) (
    Pre addStart (Start L mctx cctx w) (
    Pre nRun (if rk == 0 then RunsTo (if ent == 0 then pilotEntry3 root else if ent == 1 then synthesizeCombinationalOffR (chk9 0) root else if ent == 2 then wrapCtxOnly root else if ent == 3 then wrapDepthOnly root else if ent == 4 then synthesizeCombinationalOff root else if ent == 5 then wrapCtxSome root else wrapDepthOne root) mctx mref cctx cref w (b, D') w'
        else if rk == 1 then (∃ mctx2 : Cx, RunsTo (if ent == 0 then pilotEntry3 root else if ent == 1 then synthesizeCombinationalOffR (chk9 0) root else if ent == 2 then wrapCtxOnly root else if ent == 3 then wrapDepthOnly root else if ent == 4 then synthesizeCombinationalOff root else if ent == 5 then wrapCtxSome root else wrapDepthOne root) mctx2 mref cctx cref w (b, D') w')
        else (∃ w2 : W, RunsTo (if ent == 0 then pilotEntry3 root else if ent == 1 then synthesizeCombinationalOffR (chk9 0) root else if ent == 2 then wrapCtxOnly root else if ent == 3 then wrapDepthOnly root else if ent == 4 then synthesizeCombinationalOff root else if ent == 5 then wrapCtxSome root else wrapDepthOne root) mctx mref cctx cref w2 (b, D') w')) (
    Pre nCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    Pre nD (ExpD L.O (eA cref w w' (envAt cref w)) w) (
    Pre nG (ExpG L.O (eA cref w w' (envAt cref w)) w) (
    Pre nT (ExpTXind L (eA cref w w' (envAt cref w)) w tele) (
    Pre nPS (ExpPS L.O w) (
    Pre nProf (ExpProfOff mref cref w) (
    (if c1 then (∃ raw, PostRunOff mctx mref cctx cref w postRoot (desOf outM D') (modOf outM b) raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (conE cref w w' (envAt cref w)) (GPt (ι := ι) lvG (conE cref w w' (envAt cref w))) (PostRunOff mctx mref cctx cref w postRoot (desOf outM D')) art shHft mm (modOf outM b) (desOf outM D') p) else True))))))))))))))

noncomputable def F10 (nQ nS nC nRun nCell nD nG nT nPS nProf : Bool := true) (ent rk qk sk ck tele : Nat := 0) (addAdm addDv addStart : Bool := false)
    (lvG : Lean.Expr → Nat := lvl₀) (c1 c2 : Bool := true) (eA conE : EnvK := eS) (root postRoot art : Name := NmRoot) (outM : Nat := 0) (CV : CDRel := CVT) : Prop :=
  Exp10 nQ nS nC nRun nCell nD nG nT nPS nProf ent rk qk sk ck tele addAdm addDv addStart lvG c1 c2 eA conE root postRoot art outM CV

noncomputable def F10_real : Prop := F10
noncomputable def F10Mu_noQuiet : Prop := F10 (nQ := false)
noncomputable def F10Mu_noSynth : Prop := F10 (nS := false)
noncomputable def F10Mu_noCache : Prop := F10 (nC := false)
noncomputable def F10Mu_noRun : Prop := F10 (nRun := false)
noncomputable def F10Mu_noCell : Prop := F10 (nCell := false)
noncomputable def F10Mu_noD : Prop := F10 (nD := false)
noncomputable def F10Mu_noG : Prop := F10 (nG := false)
noncomputable def F10Mu_noT : Prop := F10 (nT := false)
noncomputable def F10Mu_noPS : Prop := F10 (nPS := false)
noncomputable def F10Mu_noProf : Prop := F10 (nProf := false)
-- the entry
noncomputable def F10Mu_entNoChecks : Prop := F10 (ent := 1)
noncomputable def F10Mu_entCtxOnly : Prop := F10 (ent := 2)
noncomputable def F10Mu_entDepthOnly : Prop := F10 (ent := 3)
noncomputable def F10Mu_entOff : Prop := F10 (ent := 4)
noncomputable def F10Mu_entCtxSome : Prop := F10 (ent := 5)
noncomputable def F10Mu_entDepthOne : Prop := F10 (ent := 6)
noncomputable def F10Mu_root : Prop := F10 (root := NmHttpX)
noncomputable def F10Mu_postRoot : Prop := F10 (postRoot := NmHttpX)
-- another Meta context / another start world for the run
noncomputable def F10Mu_runCtx : Prop := F10 (rk := 1)
noncomputable def F10Mu_runWorld : Prop := F10 (rk := 2)
-- the three residual premises at another world / in another form
noncomputable def F10Mu_quietOther : Prop := F10 (qk := 1)
noncomputable def F10Mu_quietAll : Prop := F10 (qk := 2)
noncomputable def F10Mu_quietEnd : Prop := F10 (qk := 3)
noncomputable def F10Mu_synthOther : Prop := F10 (sk := 1)
noncomputable def F10Mu_synthNone : Prop := F10 (sk := 2)
noncomputable def F10Mu_synthEnd : Prop := F10 (sk := 3)
noncomputable def F10Mu_cacheOther : Prop := F10 (ck := 1)
noncomputable def F10Mu_cacheEmpty : Prop := F10 (ck := 2)
noncomputable def F10Mu_cacheEnd : Prop := F10 (ck := 3)
-- the conjuncts the checks supply, or the whole Start, back as hypotheses
noncomputable def F10Mu_addAdm : Prop := F10 (addAdm := true)
noncomputable def F10Mu_addDv : Prop := F10 (addDv := true)
noncomputable def F10Mu_addBoth : Prop := F10 (addAdm := true) (addDv := true)
noncomputable def F10Mu_addStart : Prop := F10 (addStart := true)
-- the conclusion
noncomputable def F10Mu_reachEnd : Prop := F10 (eA := eE)
noncomputable def F10Mu_reachOther : Prop := F10 (eA := eX)
noncomputable def F10Mu_conEnd : Prop := F10 (conE := eE)
noncomputable def F10Mu_conOther : Prop := F10 (conE := eX)
noncomputable def F10Mu_teleV6 : Prop := F10 (tele := 1)
noncomputable def F10Mu_teleOrigPlain : Prop := F10 (tele := 2)
noncomputable def F10Mu_teleOrigX : Prop := F10 (tele := 3)
noncomputable def F10Mu_teleAdmStrong : Prop := F10 (tele := 4)
noncomputable def F10Mu_lvlGPt0 : Prop := F10 (lvG := lvlZero)
noncomputable def F10Mu_lvlGPtSucc : Prop := F10 (lvG := lvlSucc)
noncomputable def F10Mu_outModule : Prop := F10 (outM := 1)
noncomputable def F10Mu_outDesign : Prop := F10 (outM := 2)
noncomputable def F10Mu_artHttp : Prop := F10 (art := NmHttp)
noncomputable def F10Mu_noC1 : Prop := F10 (c1 := false)
noncomputable def F10Mu_noC2 : Prop := F10 (c2 := false)
noncomputable def F10Mu_carrierZ : Prop := F10 (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)

/-! ### expected types of the new lemmas, written again -/

-- (L4) the run lemma
noncomputable def ExpRun (cu : Nat) (dep : Nat) (stW : Nat) (chk : Environment → Name → Bool) (needCtx needDep needRun : Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {X : Name} {w w' : W} {r : Mod × Design},
    RunsTo (pilotEntry3 X) mctx mref cctx cref w r w' →
    (if needCtx then (if cu == 0 then mctx.canUnfold? = none else mctx.canUnfold?.isSome = true) else True) ∧
    (if needDep then readOf sparkleSynthDepth w = dep else True) ∧
    (if needRun then RunsTo (synthesizeCombinationalOffR chk X) mctx mref cctx cref (if stW == 0 then getW sparkleSynthDepth w else w) r w' else True)
noncomputable def ExpRun_real : Prop := ExpRun 0 0 0 (chk9 0) true true true
noncomputable def ExpRunMu_ctxSome : Prop := ExpRun 1 0 0 (chk9 0) true true true
noncomputable def ExpRunMu_dep1 : Prop := ExpRun 0 1 0 (chk9 0) true true true
noncomputable def ExpRunMu_startWorld : Prop := ExpRun 0 0 1 (chk9 0) true true true
noncomputable def ExpRunMu_v8chk : Prop := ExpRun 0 0 0 Tools.ShippingFGCircuitS3b2Final.pilotReaderOk true true true
noncomputable def ExpRunMu_noCtx : Prop := ExpRun 0 0 0 (chk9 0) false true true
noncomputable def ExpRunMu_noDep : Prop := ExpRun 0 0 0 (chk9 0) true false true
noncomputable def ExpRunMu_noRun : Prop := ExpRun 0 0 0 (chk9 0) true true false

-- (L5) AdmCtx from the run: for EVERY quiet
noncomputable def ExpAdm (_anyQuiet : Bool) (ent : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {X : Name} {w w' : W} {r : Mod × Design},
    RunsTo (if ent == 0 then pilotEntry3 X else synthesizeCombinationalOffR (chk9 0) X) mctx mref cctx cref w r w' →
    ∀ (quiet : W → Prop), AdmCtx quiet mctx cctx
noncomputable def ExpAdm_real : Prop := ExpAdm true 0
noncomputable def ExpAdmMu_noChecks : Prop := ExpAdm true 1

-- (L6) dv w = 0
noncomputable def ExpDv (ent dep : Nat) (atEnd : Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {X : Name} {w w' : W} {r : Mod × Design},
    RunsTo (if ent == 0 then pilotEntry3 X else synthesizeCombinationalOffR (chk9 0) X) mctx mref cctx cref w r w' → dv (if atEnd then w' else w) = dep
noncomputable def ExpDv_real : Prop := ExpDv 0 0 false
noncomputable def ExpDvMu_noChecks : Prop := ExpDv 1 0 false
noncomputable def ExpDvMu_dep1 : Prop := ExpDv 0 1 false
noncomputable def ExpDvMu_endWorld : Prop := ExpDv 0 0 true

-- (L7) the run behind the checks, from the same start world, given ReadWorld of the depth cell
noncomputable def ExpEntry2 (needRW : Bool) (stW : Nat) (chk : Environment → Name → Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {X : Name} {w w' : W} {r : Mod × Design},
    (if needRW then ReadWorld sparkleSynthDepth else True) →
    RunsTo (pilotEntry3 X) mctx mref cctx cref w r w' →
    RunsTo (synthesizeCombinationalOffR chk X) mctx mref cctx cref (if stW == 0 then w else getW sparkleSynthDepth w) r w'
noncomputable def ExpEntry2_real : Prop := ExpEntry2 true 0 (chk9 0)
noncomputable def ExpEntry2Mu_noRW : Prop := ExpEntry2 false 0 (chk9 0)
noncomputable def ExpEntry2Mu_afterGet : Prop := ExpEntry2 true 1 (chk9 0)
noncomputable def ExpEntry2Mu_v8chk : Prop := ExpEntry2 true 0 Tools.ShippingFGCircuitS3b2Final.pilotReaderOk

-- (L8, L9) the refusals
noncomputable def ExpRefCtx (flip : Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {f : Lean.Meta.Config → ConstantInfo → CoreM Bool},
    (if flip then mctx.canUnfold? = none else mctx.canUnfold? = some f) →
    ∀ {X : Name} {w w' : W} {r : Mod × Design}, ¬ RunsTo (pilotEntry3 X) mctx mref cctx cref w r w'
noncomputable def ExpRefCtx_real : Prop := ExpRefCtx false
noncomputable def ExpRefCtxMu_none : Prop := ExpRefCtx true
noncomputable def ExpRefDep (dep : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {X : Name} {w w' : W} {r : Mod × Design},
    readOf sparkleSynthDepth w ≠ dep → ¬ RunsTo (pilotEntry3 X) mctx mref cctx cref w r w'
noncomputable def ExpRefDep_real : Prop := ExpRefDep 0
noncomputable def ExpRefDepMu_dep1 : Prop := ExpRefDep 1

-- (L10, L11) the cache half after the core head
noncomputable def ExpJqc (D : Nat) (needQ needS needD needA : Bool) (atStart : Bool) : Prop :=
  ∀ {mctx : Cx} {cctx : Cc} {mref : Rf1} {cref : Rf2} (L : Laws mref cref) {X : Name} {w w1 : W} {s : Tools.ShippingEntryReadsLinked.CoreSaved},
    (if needA then AdmCtx L.O.quiet mctx cctx else True) → (if needQ then L.O.quiet w else True) →
    (if needS then sv w = some synthesizeChild else True) → (if needD then dv w = 0 else True) →
    RunsTo (coreHeadOff X) mctx mref cctx cref w s w1 → JQC L.O D (if atStart then w else w1)
noncomputable def ExpJqc_real : Prop := ExpJqc 1 true true true true false
noncomputable def ExpJqcMu_depth0 : Prop := ExpJqc 0 true true true true false
noncomputable def ExpJqcMu_depth2 : Prop := ExpJqc 2 true true true true false
noncomputable def ExpJqcMu_atStart : Prop := ExpJqc 1 true true true true true
noncomputable def ExpJqcMu_noQuiet : Prop := ExpJqc 1 false true true true false
noncomputable def ExpJqcMu_noSynth : Prop := ExpJqc 1 true false true true false
noncomputable def ExpJqcMu_noDv : Prop := ExpJqc 1 true true false true false
noncomputable def ExpJqcMu_noAdm : Prop := ExpJqc 1 true true true false false
noncomputable def ExpJqcRun (D : Nat) (needQ needS needRW : Bool) (stJ : Bool) : Prop :=
  ∀ {mctx : Cx} {cctx : Cc} {mref : Rf1} {cref : Rf2} (L : Laws mref cref) {w w' : W} {r : Mod × Design},
    (if needRW then ReadWorld sparkleSynthDepth else True) →
    RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w r w' →
    (if needQ then L.O.quiet w else True) → (if needS then sv w = some synthesizeChild else True) →
    ∃ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 : W),
      RunsTo (coreHeadOff hftRoot) mctx mref cctx cref w s w1 ∧ JQC L.O D (if stJ then w else w1)
noncomputable def ExpJqcRun_real : Prop := ExpJqcRun 1 true true true false
noncomputable def ExpJqcRunMu_depth0 : Prop := ExpJqcRun 0 true true true false
noncomputable def ExpJqcRunMu_atStart : Prop := ExpJqcRun 1 true true true true
noncomputable def ExpJqcRunMu_noQuiet : Prop := ExpJqcRun 1 false true true false
noncomputable def ExpJqcRunMu_noSynth : Prop := ExpJqcRun 1 true false true false
noncomputable def ExpJqcRunMu_noRW : Prop := ExpJqcRun 1 true true false false

-- (L12) Start from the residual and the run
noncomputable def ExpStartRes (needQ needS needC : Bool) (cacheAt : Nat) (conj : Nat) : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} (L : Laws mref cref) {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w' →
    (if needQ then L.O.quiet w else True) → (if needS then sv w = some synthesizeChild else True) →
    (if needC then CacheInvA L.O (cv (if cacheAt == 0 then w else w')) else True) →
    (if conj == 0 then Start L mctx cctx w else if conj == 1 then (L.O.quiet w ∧ sv w = some synthesizeChild ∧ dv w = 0 ∧ CacheInvA L.O (cv w)) else (AdmCtx L.O.quiet mctx cctx ∧ L.O.quiet w))
noncomputable def ExpStartRes_real : Prop := ExpStartRes true true true 0 0
noncomputable def ExpStartResMu_noQuiet : Prop := ExpStartRes false true true 0 0
noncomputable def ExpStartResMu_noSynth : Prop := ExpStartRes true false true 0 0
noncomputable def ExpStartResMu_noCache : Prop := ExpStartRes true true false 0 0
noncomputable def ExpStartResMu_cacheEnd : Prop := ExpStartRes true true true 1 0
noncomputable def ExpStartResMu_noAdm : Prop := ExpStartRes true true true 0 1
noncomputable def ExpStartResMu_partial : Prop := ExpStartRes true true true 0 2

-- (L14, L15) frameT for Throws
noncomputable def ExpEndWThrows (needM needC : Bool) (atEnd : Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2}, (if needM then ReadWorld mref else True) → (if needC then ReadWorld cref else True) →
    ∀ {α : Type} {p : MetaM α}, Throws p → ∀ (w : W), endW mctx mref cctx cref p w = (if atEnd then getW cref w else w)
noncomputable def ExpEndWThrows_real : Prop := ExpEndWThrows true true false
noncomputable def ExpEndWThrowsMu_noM : Prop := ExpEndWThrows false true false
noncomputable def ExpEndWThrowsMu_noC : Prop := ExpEndWThrows true false false
noncomputable def ExpEndWThrowsMu_afterGet : Prop := ExpEndWThrows true true true

/-- the field `RefLawsAOps.frameT`'s proposition, written again (and a variant per slot) -/
noncomputable def ExpFrameT (needM needC : Bool) (needHq : Bool) (conj : Nat) : Prop :=
  ∀ {mref : Rf1} {cref : Rf2}, (if needM then ReadWorld mref else True) → (if needC then ReadWorld cref else True) →
    ∀ (quiet : W → Prop) {mctx : Cx} {cctx : Cc} {α : Type}, AdmCtx quiet mctx cctx →
      ∀ (p : MetaM α), Throws p → ∀ w, (if needHq then quiet w else True) →
      (if conj == 0 then ((cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧ dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w))
       else if conj == 1 then (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧ dv (endW mctx mref cctx cref p w) = dv w)
       else ((cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧ dv (endW mctx mref cctx cref p w) = dv w + 1) ∧ quiet (endW mctx mref cctx cref p w)))
noncomputable def ExpFrameT_real : Prop := ExpFrameT true true true 0
noncomputable def ExpFrameTMu_noM : Prop := ExpFrameT false true true 0
noncomputable def ExpFrameTMu_noC : Prop := ExpFrameT true false true 0
noncomputable def ExpFrameTMu_noQuietPre : Prop := ExpFrameT true true false 0
noncomputable def ExpFrameTMu_noQuietPost : Prop := ExpFrameT true true true 1
noncomputable def ExpFrameTMu_depthPlus1 : Prop := ExpFrameT true true true 2

/-- the unfolding path of THIS Check: Check48's `norm48` list plus v10 -/
def unfold50 : List Name := unfold48 ++ [``Tools.ShippingFGCircuitS3jFinal.HftFinalStmtOffCombined10]
def norm50 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold50.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  Tests.Gen5.FGCircuitPilotCheck47.normC e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck50 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- (A) the complete type of v10
  let f10ty ← tyOf ``Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10
  let f10 ← norm50 f10ty
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined10" f10 (← norm50 (Q "F10_real"))
  -- the statement def and the theorem agree
  Tests.Gen5.FGCircuitCmp.checkSame "HftFinalStmtOffCombined10 = the theorem's type" f10 (← norm50 (Lean.mkConst ``Tools.ShippingFGCircuitS3jFinal.HftFinalStmtOffCombined10))
  for mu in ["F10Mu_noQuiet", "F10Mu_noSynth", "F10Mu_noCache", "F10Mu_noRun", "F10Mu_noCell", "F10Mu_noD", "F10Mu_noG", "F10Mu_noT", "F10Mu_noPS", "F10Mu_noProf",
      "F10Mu_entNoChecks", "F10Mu_entCtxOnly", "F10Mu_entDepthOnly", "F10Mu_entOff", "F10Mu_entCtxSome", "F10Mu_entDepthOne", "F10Mu_root", "F10Mu_postRoot",
      "F10Mu_runCtx", "F10Mu_runWorld",
      "F10Mu_quietOther", "F10Mu_quietAll", "F10Mu_quietEnd", "F10Mu_synthOther", "F10Mu_synthNone", "F10Mu_synthEnd", "F10Mu_cacheOther", "F10Mu_cacheEmpty", "F10Mu_cacheEnd",
      "F10Mu_addAdm", "F10Mu_addDv", "F10Mu_addBoth", "F10Mu_addStart",
      "F10Mu_reachEnd", "F10Mu_reachOther", "F10Mu_conEnd", "F10Mu_conOther", "F10Mu_teleV6", "F10Mu_teleOrigPlain", "F10Mu_teleOrigX", "F10Mu_teleAdmStrong",
      "F10Mu_lvlGPt0", "F10Mu_lvlGPtSucc", "F10Mu_outModule", "F10Mu_outDesign", "F10Mu_artHttp", "F10Mu_noC1", "F10Mu_noC2", "F10Mu_carrierZ"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined10 vs {mu}" f10 (← norm50 (Q mu)); nm := nm + 1
  -- v10 is none of the earlier statements
  for (what, c) in [("v9", ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9), ("v8", ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8),
      ("v7", ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7)] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined10 vs the {what} theorem's type" f10 (← norm50 (← tyOf c)); nm := nm + 1
  -- (B) the new lemmas, each against its expected type and its mutants
  let mut nmL : Nat := 0
  let lemmas : List (Name × String × List String) := [
    (``Tools.ShippingFGCircuitS3jStart.pilotEntry3_run, "ExpRun_real", ["ExpRunMu_ctxSome", "ExpRunMu_dep1", "ExpRunMu_startWorld", "ExpRunMu_v8chk", "ExpRunMu_noCtx", "ExpRunMu_noDep", "ExpRunMu_noRun"]),
    (``Tools.ShippingFGCircuitS3jStart.admCtx_of_pilotEntry3, "ExpAdm_real", ["ExpAdmMu_noChecks"]),
    (``Tools.ShippingFGCircuitS3jStart.dv_of_pilotEntry3, "ExpDv_real", ["ExpDvMu_noChecks", "ExpDvMu_dep1", "ExpDvMu_endWorld"]),
    (``Tools.ShippingFGCircuitS3jStart.entry2_of_pilotEntry3, "ExpEntry2_real", ["ExpEntry2Mu_noRW", "ExpEntry2Mu_afterGet", "ExpEntry2Mu_v8chk"]),
    (``Tools.ShippingFGCircuitS3jStart.pilotEntry3_refuses_canUnfold, "ExpRefCtx_real", ["ExpRefCtxMu_none"]),
    (``Tools.ShippingFGCircuitS3jStart.pilotEntry3_refuses_depth, "ExpRefDep_real", ["ExpRefDepMu_dep1"]),
    (``Tools.ShippingFGCircuitS3jStart.jqc_after_head, "ExpJqc_real", ["ExpJqcMu_depth0", "ExpJqcMu_depth2", "ExpJqcMu_atStart", "ExpJqcMu_noQuiet", "ExpJqcMu_noSynth", "ExpJqcMu_noDv", "ExpJqcMu_noAdm"]),
    (``Tools.ShippingFGCircuitS3jStart.jqc_after_head_of_pilotEntry3, "ExpJqcRun_real", ["ExpJqcRunMu_depth0", "ExpJqcRunMu_atStart", "ExpJqcRunMu_noQuiet", "ExpJqcRunMu_noSynth", "ExpJqcRunMu_noRW"]),
    (``Tools.ShippingFGCircuitS3jFinal.start_of_residual, "ExpStartRes_real", ["ExpStartResMu_noQuiet", "ExpStartResMu_noSynth", "ExpStartResMu_noCache", "ExpStartResMu_cacheEnd", "ExpStartResMu_noAdm", "ExpStartResMu_partial"]),
    (``Tools.ShippingFGCircuitS3jThrows.endW_throws, "ExpEndWThrows_real", ["ExpEndWThrowsMu_noM", "ExpEndWThrowsMu_noC", "ExpEndWThrowsMu_afterGet"]),
    (``Tools.ShippingFGCircuitS3jThrows.frameT_of_readWorld, "ExpFrameT_real", ["ExpFrameTMu_noM", "ExpFrameTMu_noC", "ExpFrameTMu_noQuietPre", "ExpFrameTMu_noQuietPost", "ExpFrameTMu_depthPlus1"])]
  for (n, real, mus) in lemmas do
    let t ← norm50 (← tyOf n)
    Tests.Gen5.FGCircuitCmp.checkSame s!"{n}" t (← norm50 (Q real))
    for mu in mus do
      Tests.Gen5.FGCircuitCmp.checkDiff s!"{n} vs {mu}" t (← norm50 (Q mu)); nmL := nmL + 1
  logInfo m!"FGCIRCUIT50 SIGNATURES: the complete type of synth_hftPcieOutByte_finalOffCombined10 equals the independently written Exp10 under ONE criterion (FGCircuitCmp.stmtEq after the ONE normalisation function norm50 = Check47.normC with the v10 statement def unfolded, applied to the real type, the expected statement and every mutant); {nm} mutants rejected (each premise dropped; the entry = no checks / only the canUnfold? check / only the depth check / the ordinary Off entry / the checks reversed; another Meta context; another start world; each residual premise at another world, at the end world, or in another form (all-worlds quiet, sv = none, an EMPTY cache); the checks' conjuncts or the whole Start back as hypotheses; the conclusion's environments, tele, level, output, artifact, carrier; v9, v8, v7's types); the complete types of the {lemmas.length} new lemmas equal their independently written expected types, {nmL} mutants rejected"
  -- (C) BINDERS and the field-level comparison with Start
  let bl (t : Lean.Expr) : MetaM (List Name) := do return binderNames ((← unfoldDefinition? t).getD t)
  let b9 ← bl (← tyOf ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9)
  let b10 ← bl f10ty
  unless b9 == [`ι, `mref, `cref, `L, `mctx, `cctx, `w, `w', `b, `D', `hstart, `hr, `hcell, `hD, `hG, `hT, `hs, `h0] do throwError "v9 binders: {b9}"
  unless b10 == [`ι, `mref, `cref, `L, `mctx, `cctx, `w, `w', `b, `D', `hquiet, `hsynth, `hcache, `hr, `hcell, `hD, `hG, `hT, `hs, `h0] do throwError "v10 binders: {b10}"
  unless b10 == (b9.filter (· != `hstart)).take 10 ++ [`hquiet, `hsynth, `hcache] ++ (b9.filter (· != `hstart)).drop 10 do throwError "v10 is not v9 with hstart replaced by hquiet hsynth hcache"
  -- field level: the conjuncts of `Start` at v10's own variables, each either one of v10's three residual binders or gone
  let conjuncts ← Meta.forallTelescope ((← unfoldDefinition? f10ty).getD f10ty) fun xs _ => do
    let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName)
    let find (n : Name) : MetaM Lean.Expr := do
      let some i := names.findIdx? (· == n) | throwError "no binder {n}"
      pure xs[i]!
    let st ← mkAppM ``Tools.ShippingGen2.Start #[← find `L, ← find `mctx, ← find `cctx, ← find `w]
    let st ← whnfD st
    -- split by hand: Start = AdmCtx ∧ JQC; JQC = JQ ∧ Cache; JQ = quiet ∧ sv ∧ dv
    let some (adm, jqc) := st.and? | throwError "Start is not a conjunction: {st}"
    let jqc ← whnfD jqc
    let some (jq, cache) := jqc.and? | throwError "JQC is not a conjunction"
    let jq ← whnfD jq
    let some (qu, rest) := jq.and? | throwError "JQ is not a conjunction"
    let some (sy, dd) := rest.and? | throwError "JQ rest is not a conjunction"
    let hyps ← [`hquiet, `hsynth, `hcache].mapM fun n => do inferType (← find n)
    let cs : List (String × Lean.Expr) := [("AdmCtx", adm), ("quiet w", qu), ("sv w = some synthesizeChild", sy), ("dv w = 0", dd), ("CacheInvA (cv w)", cache)]
    let mut gone : List String := []
    let mut kept : List String := []
    for (nm, c) in cs do
      let mut found := false
      for h in hyps do
        if ← isDefEq h c then found := true
      if found then kept := kept ++ [nm] else gone := gone ++ [nm]
    pure (kept, gone)
  unless conjuncts.1 == ["quiet w", "sv w = some synthesizeChild", "CacheInvA (cv w)"] && conjuncts.2 == ["AdmCtx", "dv w = 0"] do
    throwError "field-level Start comparison: kept {conjuncts.1}, gone {conjuncts.2}"
  logInfo m!"FGCIRCUIT50 BINDERS (9 implicit + explicit): v9 ({b9.length} = 9 + 9) {b9}; v10 ({b10.length} = 9 + 11) {b10}; v10 = v9 with hstart replaced by hquiet hsynth hcache; Start's five conjuncts at v10's own variables: kept as v10 hypotheses {conjuncts.1}; gone (supplied by the run's own checks) {conjuncts.2}"

/-! ## (D) Lean-checked field-level facts: `Start` is exactly five conjuncts; the vacuous `L` -/

theorem start_fields {mref : Rf1} {cref : Rf2} (L : Laws mref cref) (mctx : Cx) (cctx : Cc) (w : W) :
    Start L mctx cctx w ↔ (AdmCtx L.O.quiet mctx cctx ∧ L.O.quiet w ∧ sv w = some synthesizeChild ∧ dv w = 0 ∧ CacheInvA L.O (cv w)) :=
  ⟨fun h => ⟨h.1, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩, fun h => ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩⟩

/-- the vacuous `L` does not satisfy the residual premises (and so is not counted as a witness of `Start`) -/
theorem vac_not_witness {mref : Rf1} {cref : Rf2} (mctx : Cx) (cctx : Cc) (w : W) :
    ¬ (Tools.ShippingFGCircuitS3jFinal.vacuousLaws mref cref).O.quiet w ∧
    ¬ Start (Tools.ShippingFGCircuitS3jFinal.vacuousLaws mref cref) mctx cctx w ∧
    AdmCtx (Tools.ShippingFGCircuitS3jFinal.vacuousLaws mref cref).O.quiet mctx cctx :=
  ⟨Tools.ShippingFGCircuitS3jFinal.vacuous_no_hquiet w, Tools.ShippingFGCircuitS3jFinal.vacuous_no_start mctx cctx w, Tools.ShippingFGCircuitS3jFinal.vacuous_adm_trivial mctx cctx⟩

-- the vacuous `L` is not used by v10's proof: its proof term (transitively, through every constant it uses) mentions neither the vacuous witness nor `quietFalse` nor `admCtx_quietFalse`
run_cmd liftTermElabM do
  let env ← getEnv
  let bad : List Name := [``Tools.ShippingFGCircuitS3jFinal.vacuousLaws, ``Tools.ShippingChildInvA.RefLawsAOps.quietFalse, ``Tools.ShippingChildInvA.RefLawsATele.quietFalse,
    ``Tools.ShippingChildInvA.admCtx_quietFalse, ``Tools.ShippingChildInvA.admCtx_quietFalse_writer, ``Tools.ShippingChildInvA.frame_quietFalse_vacuous]
  let mut seen : NameSet := {}
  let mut todo : List Name := [``Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10]
  let mut hit : List Name := []
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
      if let some ci := env.find? n then
        for c in ci.getUsedConstantsAsSet.toList do
          unless seen.contains c do todo := c :: todo
  unless fuel > 0 do throwError "the dependency walk ran out of fuel"
  unless hit.isEmpty do throwError "FGCIRCUIT50 VACUITY: v10's proof reaches {hit}"
  logInfo m!"FGCIRCUIT50 VACUITY: the vacuous L (quiet := False) is constructed (vacuousLaws) and refuted as a witness: hquiet fails at every world, Start fails (vac_not_witness), and the check's AdmCtx holds at quiet := False too (it carries no information on quiet); the proof of v10 reaches {seen.size} constants and none of vacuousLaws / RefLawsAOps.quietFalse / RefLawsATele.quietFalse / admCtx_quietFalse(_writer) / frame_quietFalse_vacuous"

/-! ## (E) executable controls of the entry in the real Meta context -/
run_cmd liftTermElabM do
  let X := hftRoot
  let ok (b : Bool) (msg : String) : MetaM Unit := unless b do throwError "FGCIRCUIT50 control failed: {msg}"
  let rp (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) : String := toString (repr m) ++ "\n" ++ toString (repr d)
  -- the real context: no canUnfold? callback (mkMetaContext), depth 0: the entry runs
  let ctx ← readThe Meta.Context
  ok ctx.canUnfold?.isNone "the run_cmd / liftTermElabM Meta context has no canUnfold? callback"
  ok ((← sparkleSynthDepth.get) == 0) "the depth reads 0 in the real context"
  let (m3, d3, v3) ← Tools.ShippingFGCircuitS3jFinal.pilotArtifact3 X
  let (m2, d2, v2) ← Tools.ShippingFGCircuitS3f2Final.pilotArtifact2 X
  let (m0, d0) ← Sparkle.Compiler.Elab.synthesizeCombinationalOff X
  unless rp m3 d3 == rp m2 d2 && rp m3 d3 == rp m0 d0 do throwError "FGCIRCUIT50 OUTPUT: the S3j entry, the S3f2 entry and the ordinary Off entry differ"
  unless v3 == v2 && v3 == Sparkle.Compiler.Elab.verilogOf m0 do throwError "FGCIRCUIT50 OUTPUT: the printed text differs"
  let (mH, dH) ← Sparkle.Compiler.Elab.synthesizeCombinationalOff hftHttp
  unless rp mH dH != rp m3 d3 do throwError "FGCIRCUIT50 OUTPUT control: another declaration's artifact compares equal"
  unless rp { m3 with name := m3.name ++ "x" } d3 != rp m0 d0 do throwError "FGCIRCUIT50 OUTPUT control: an altered Module compares equal"
  -- another Meta context: a canUnfold? callback present -> an explicit error, no output
  let cb : Meta.Config → ConstantInfo → CoreM Bool := fun _ _ => pure true
  let msgCtx ← try
      discard <| withTheReader Meta.Context (fun c => { c with canUnfold? := some cb }) (Tools.ShippingFGCircuitS3jStart.pilotEntry3 X)
      pure "NO ERROR"
    catch e => e.toMessageData.toString
  unless msgCtx.contains "canUnfold?" do throwError "FGCIRCUIT50 CONTROL (another Meta context): {msgCtx}"
  -- the same context with the check-free S3f2 entry: it does run (the callback is not what the old entry looked at), so the refusal is the new check's
  discard <| withTheReader Meta.Context (fun c => { c with canUnfold? := some cb }) (Tools.ShippingFGCircuitS3f2Final.pilotEntry2 X)
  -- depth not 0: an explicit error, and the depth cell is left as found
  let savedDepth ← sparkleSynthDepth.get
  sparkleSynthDepth.set 1
  let msgDepth ← try
      discard <| Tools.ShippingFGCircuitS3jStart.pilotEntry3 X
      pure "NO ERROR"
    catch e => e.toMessageData.toString
  sparkleSynthDepth.set savedDepth
  unless msgDepth.contains "depth" do throwError "FGCIRCUIT50 CONTROL (depth 1): {msgDepth}"
  ok ((← sparkleSynthDepth.get) == savedDepth) "the depth cell restored"
  -- a non-empty start cache: the entry still runs and returns the same artifact (the core head clears the cache; the cache half of Start is not what the run needs)
  let savedCache ← Sparkle.Compiler.Elab.sparkleChildCache.get
  Sparkle.Compiler.Elab.sparkleChildCache.set (({} : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)).insert hftHttp (mH, dH))
  let (mN, dN, vN) ← Tools.ShippingFGCircuitS3jFinal.pilotArtifact3 X
  Sparkle.Compiler.Elab.sparkleChildCache.set savedCache
  unless rp mN dN == rp m3 d3 && vN == v3 do throwError "FGCIRCUIT50 CONTROL (non-empty cache): the artifact changed"
  logInfo m!"FGCIRCUIT50 OUTPUT: module+design repr of the S3j entry = the S3f2 entry = the ordinary Off entry ({(toString (repr m3)).length} / {(toString (repr d3)).length} chars); the printed text from the S3j run's own Module is identical ({v3.length} chars); controls: another declaration's artifact and an altered Module compare unequal; the real run_cmd context has no canUnfold? callback and depth 0; a canUnfold? callback in the Meta context gives an explicit error from the S3j entry while the S3f2 entry still runs; depth 1 gives an explicit error and the depth cell is restored; a NON-EMPTY start cache leaves the artifact unchanged (so the cache half of Start is not needed by the run)"

/-! ## (F) AXIOMS -/
run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3jStart.runsTo_readThe, ``Tools.ShippingFGCircuitS3jStart.runsTo_readThe_bind, ``Tools.ShippingFGCircuitS3jStart.runsTo_get,
    ``Tools.ShippingFGCircuitS3jStart.pilotEntry3_run, ``Tools.ShippingFGCircuitS3jStart.pilotEntry3_refuses_canUnfold, ``Tools.ShippingFGCircuitS3jStart.pilotEntry3_refuses_depth,
    ``Tools.ShippingFGCircuitS3jStart.admCtx_of_pilotEntry3, ``Tools.ShippingFGCircuitS3jStart.dv_of_pilotEntry3, ``Tools.ShippingFGCircuitS3jStart.entry2_of_pilotEntry3,
    ``Tools.ShippingFGCircuitS3jStart.jqc_after_head, ``Tools.ShippingFGCircuitS3jStart.jqc_after_head_of_pilotEntry3,
    ``Tools.ShippingFGCircuitS3jFinal.start_of_residual, ``Tools.ShippingFGCircuitS3jFinal.synth_hftPcieOutByte_finalOffCombined10,
    ``Tools.ShippingFGCircuitS3jFinal.vacuous_no_hquiet, ``Tools.ShippingFGCircuitS3jFinal.vacuous_no_start, ``Tools.ShippingFGCircuitS3jFinal.vacuous_adm_trivial,
    ``Tools.ShippingFGCircuitS3jThrows.endW_throws, ``Tools.ShippingFGCircuitS3jThrows.frameT_of_readWorld, ``Tests.Gen5.FGCircuitPilotCheck50.start_fields, ``Tests.Gen5.FGCircuitPilotCheck50.vac_not_witness]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT50 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck50
