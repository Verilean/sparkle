import Tools.ShippingFGCircuitS3f2Final
import Tests.Gen5.FGCircuitPilotCheck47
set_option autoImplicit false
-- FG circuit pilot Check48 (S3f2): the checker `pilotReaderOk2` and the entry (controls on the real environment: root name / type / value / levelParams / reader data / gates / start environment; the output against the existing entries), the complete type of v9 (9 binders: no env₀, no hchk) against an independently written statement under ONE normalisation function, the type of pilotReaderOk2_sound and of the RootReader → ReaderAt bridge, mutants, the binder list (v9 = v8 − [env₀, hchk]) and standard axioms only.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck48
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


def eX : EnvK := fun cref w _ _ => envX (envAt cref w)

/-- the checker of the entry, written out: 0 = `pilotReaderOk2` written as its four conjuncts; 1 = `pilotReaderOk` (v8's); 3 = True; 4-8 = the conjunct dropped (4 no root reader, 5 no gates, 6 no root definition, 7 no children / name check); 9 = the root reader at another level; 10 = the root reader against the HTTP child's data -/
def chk9 (k : Nat) : Environment → Name → Bool :=
  if k == 1 then Tools.ShippingFGCircuitS3b2Final.pilotReaderOk
  else if k == 3 then (fun _ _ => true)
  else if k == 4 then (fun env X => pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && entryGatesB env X)
  else if k == 5 then (fun env X => pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && rootReaderB lvl₀ env X rootMD)
  else if k == 6 then (fun env X => pilotReaderOk env X && entryGatesB env X && rootReaderB lvl₀ env X rootMD)
  else if k == 7 then (fun env X => rootDefB env X hftRootType hftRootValue && entryGatesB env X && rootReaderB lvl₀ env X rootMD)
  else if k == 9 then (fun env X => pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && entryGatesB env X && rootReaderB lvlSucc env X rootMD)
  else if k == 10 then (fun env X => pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && entryGatesB env X && rootReaderB lvl₀ env X Tools.ShippingFGCircuitS3b2Exp.httpMD)
  else (fun env X => pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && entryGatesB env X && rootReaderB lvl₀ env X rootMD)

def modOf (k : Nat) (b : Mod) : Mod := if k == 1 then { b with name := b.name ++ "x" } else if k == 3 then { b with name := b.name ++ "x" } else b
def desOf (k : Nat) (D : Design) : Design := if k == 2 then { D with modules := [] } else if k == 3 then { D with modules := [] } else D

/-- **v9, written again** (no `env₀`, no `hchk`: the start environment of every statement is `envAt cref w`). Knobs: the premises (Bool); `ent` = the run's entry (0 = `synthesizeCombinationalOffR` with the checker `chk9 0`, 1, 3-10 = another checker (`chk9`), 2 = the ordinary Off entry); `st` the start premise; `tele` (`ExpTXind`); the reach environment `eA`, the conclusion's environment `conE`; the root, post-run root, artifact name; the level of `GPt`; conclusion parts; Module / Design; carrier. `back` (0 none, 1 = `env₀` and `hchk` back (v8's premises), 2 = `env₀` alone back) are separate statements `Exp9b`. -/
noncomputable def Exp9 (nStart nRun nCell nD nG nT nPS nProf : Bool) (ent st tele : Nat)
    (lvG : Lean.Expr → Nat) (c1 c2 : Bool) (eA conE : EnvK) (root postRoot art : Name) (outM : Nat) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Pre nStart (if st == 0 then Start L mctx cctx w else if st == 1 then (∃ mctx2 : Cx, Start L mctx2 cctx w) else (∃ w2 : W, Start L mctx cctx w2)) (
    Pre nRun (RunsTo (if ent == 2 then synthesizeCombinationalOff root else synthesizeCombinationalOffR (chk9 ent) root) mctx mref cctx cref w (b, D') w') (
    Pre nCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    Pre nD (ExpD L.O (eA cref w w' (envAt cref w)) w) (
    Pre nG (ExpG L.O (eA cref w w' (envAt cref w)) w) (
    Pre nT (ExpTXind L (eA cref w w' (envAt cref w)) w tele) (
    Pre nPS (ExpPS L.O w) (
    Pre nProf (ExpProfOff mref cref w) (
    (if c1 then (∃ raw, PostRunOff mctx mref cctx cref w postRoot (desOf outM D') (modOf outM b) raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (conE cref w w' (envAt cref w)) (GPt (ι := ι) lvG (conE cref w w' (envAt cref w))) (PostRunOff mctx mref cctx cref w postRoot (desOf outM D')) art shHft mm (modOf outM b) (desOf outM D') p) else True)))))))))

/-- the v8-shaped statements with the checker of v9: `env₀` back (`needChk` false), or `env₀` and `hchk` (at level `lvC`, environment `chkE`) back -/
noncomputable def Exp9b (needChk : Bool) (lvC : Lean.Expr → Nat) (chkE : EnvK) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinationalOffR (chk9 0) NmRoot) mctx mref cctx cref w (b, D') w' →
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref →
    Pre needChk (CheckedStart lvC (chkE cref w w' env₀) cref w NmRoot hftRootType hftRootValue RootData) (
    ExpD L.O (envAt cref w) w →
    ExpG L.O (envAt cref w) w →
    ExpTXind L (envAt cref w) w 0 →
    ExpPS L.O w →
    ExpProfOff mref cref w →
    (∃ raw, PostRunOff mctx mref cctx cref w NmRoot D' b raw) ∧
    (∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CVT (envAt cref w) (GPt (ι := ι) lvl₀ (envAt cref w)) (PostRunOff mctx mref cctx cref w NmRoot D') NmRoot shHft mm b D' p))

noncomputable def F9 (nStart nRun nCell nD nG nT nPS nProf : Bool := true) (ent st tele : Nat := 0)
    (lvG : Lean.Expr → Nat := lvl₀) (c1 c2 : Bool := true) (eA conE : EnvK := eS) (root postRoot art : Name := NmRoot) (outM : Nat := 0) (CV : CDRel := CVT) : Prop :=
  Exp9 nStart nRun nCell nD nG nT nPS nProf ent st tele lvG c1 c2 eA conE root postRoot art outM CV

noncomputable def F9_real : Prop := F9
noncomputable def F9Mu_noStart : Prop := F9 (nStart := false)
noncomputable def F9Mu_noRun : Prop := F9 (nRun := false)
noncomputable def F9Mu_noCell : Prop := F9 (nCell := false)
noncomputable def F9Mu_noD : Prop := F9 (nD := false)
noncomputable def F9Mu_noG : Prop := F9 (nG := false)
noncomputable def F9Mu_noT : Prop := F9 (nT := false)
noncomputable def F9Mu_noPS : Prop := F9 (nPS := false)
noncomputable def F9Mu_noProf : Prop := F9 (nProf := false)
-- the entry
noncomputable def F9Mu_entV8 : Prop := F9 (ent := 1)
noncomputable def F9Mu_entOff : Prop := F9 (ent := 2)
noncomputable def F9Mu_entTrue : Prop := F9 (ent := 3)
noncomputable def F9Mu_entNoReader : Prop := F9 (ent := 4)
noncomputable def F9Mu_entNoGates : Prop := F9 (ent := 5)
noncomputable def F9Mu_entNoRootDef : Prop := F9 (ent := 6)
noncomputable def F9Mu_entNoChildren : Prop := F9 (ent := 7)
noncomputable def F9Mu_entRootLvl : Prop := F9 (ent := 9)
noncomputable def F9Mu_entRootData : Prop := F9 (ent := 10)
noncomputable def F9Mu_root : Prop := F9 (root := NmHttpX)
noncomputable def F9Mu_postRoot : Prop := F9 (postRoot := NmHttpX)
-- the start world / context
noncomputable def F9Mu_startCtx : Prop := F9 (st := 1)
noncomputable def F9Mu_startWorld : Prop := F9 (st := 2)
-- the start environment: the reach and the conclusion at another environment
noncomputable def F9Mu_reachEnd : Prop := F9 (eA := eE)
noncomputable def F9Mu_reachOther : Prop := F9 (eA := eX)
noncomputable def F9Mu_conEnd : Prop := F9 (conE := eE)
noncomputable def F9Mu_conOther : Prop := F9 (conE := eX)
-- hT
noncomputable def F9Mu_teleV6 : Prop := F9 (tele := 1)
noncomputable def F9Mu_teleOrigPlain : Prop := F9 (tele := 2)
noncomputable def F9Mu_teleOrigX : Prop := F9 (tele := 3)
noncomputable def F9Mu_teleAdmStrong : Prop := F9 (tele := 4)
noncomputable def F9Mu_teleNoReach : Prop := F9 (tele := 5)
noncomputable def F9Mu_teleNoReads : Prop := F9 (tele := 6)
-- the level, the output, the conclusion, the carrier
noncomputable def F9Mu_lvlGPt0 : Prop := F9 (lvG := lvlZero)
noncomputable def F9Mu_lvlGPtSucc : Prop := F9 (lvG := lvlSucc)
noncomputable def F9Mu_outModule : Prop := F9 (outM := 1)
noncomputable def F9Mu_outDesign : Prop := F9 (outM := 2)
noncomputable def F9Mu_outBoth : Prop := F9 (outM := 3)
noncomputable def F9Mu_artHttp : Prop := F9 (art := NmHttp)
noncomputable def F9Mu_noC1 : Prop := F9 (c1 := false)
noncomputable def F9Mu_noC2 : Prop := F9 (c2 := false)
noncomputable def F9Mu_carrierZ : Prop := F9 (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)
noncomputable def F9Mu_carrierOld : Prop := F9 (CV := Tools.ShippingFGCircuitS1tFinal.cdvOld)
-- the removed binders back: env₀ and hchk (at the start / another / the end environment, at lvl₀ / another level), env₀ alone
noncomputable def F9Mu_hchkBack : Prop := Exp9b true lvl₀ e0
noncomputable def F9Mu_hchkBackLvl : Prop := Exp9b true lvlSucc e0
noncomputable def F9Mu_hchkBackStartEnv : Prop := Exp9b true lvl₀ eS
noncomputable def F9Mu_hchkBackEndEnv : Prop := Exp9b true lvl₀ eE
noncomputable def F9Mu_env0Back : Prop := Exp9b false lvl₀ e0

/-- (soundness of the check, written again) knobs: the check, the environments of the check / of the conclusions, the levels, the children's names / data, the root's name / type / value / data -/
noncomputable def ExpSnd2 (chk : Environment → Name → Bool) (ec ee er : Environment → Environment) (lv lvR : Lean.Expr → Nat)
    (nH nT nR : Name) (dH dT dR : MachineData) (tyR valR : Lean.Expr) (needRoot : Bool) : Prop :=
  ∀ {env : Environment} {X : Name}, chk (ec env) X = true →
    (if needRoot then X = hftRoot else True) ∧ RootReader lv (ee env) nH dH ∧ RootReader lv (ee env) nT dT ∧
    CheckedEnv lvR (er env) nR tyR valR dR

noncomputable def Snd2 (chk : Environment → Name → Bool := chk9 0) (ec ee er : Environment → Environment := fun e => e)
    (lv lvR : Lean.Expr → Nat := lvl₀) (nH : Name := NmHttp) (nT : Name := NmTlp) (nR : Name := hftRoot)
    (dH : MachineData := HttpData) (dT : MachineData := TlpData) (dR : MachineData := RootData)
    (tyR : Lean.Expr := hftRootType) (valR : Lean.Expr := hftRootValue) (needRoot : Bool := true) : Prop :=
  ExpSnd2 chk ec ee er lv lvR nH nT nR dH dT dR tyR valR needRoot

noncomputable def Snd2_real : Prop := Snd2
noncomputable def Snd2Mu_true : Prop := Snd2 (chk := chkTrue)
noncomputable def Snd2Mu_v8chk : Prop := Snd2 (chk := pilotReaderOk)
noncomputable def Snd2Mu_envCheck : Prop := Snd2 (ec := envX)
noncomputable def Snd2Mu_envChildren : Prop := Snd2 (ee := envX)
noncomputable def Snd2Mu_envRoot : Prop := Snd2 (er := envX)
noncomputable def Snd2Mu_lvlChildren : Prop := Snd2 (lv := lvlSucc)
noncomputable def Snd2Mu_lvlRoot0 : Prop := Snd2 (lvR := lvlZero)
noncomputable def Snd2Mu_lvlRootSucc : Prop := Snd2 (lvR := lvlSucc)
noncomputable def Snd2Mu_rootName : Prop := Snd2 (nR := NmHttp)
noncomputable def Snd2Mu_rootType : Prop := Snd2 (tyR := hftRootValue)
noncomputable def Snd2Mu_rootValue : Prop := Snd2 (valR := hftRootType)
noncomputable def Snd2Mu_rootData : Prop := Snd2 (dR := HttpData)
noncomputable def Snd2Mu_swapChildren : Prop := Snd2 (dH := TlpData) (dT := HttpData)
noncomputable def Snd2Mu_noRoot : Prop := Snd2 (needRoot := false)
noncomputable def Snd2Mu_noCheckedEnv : Prop :=
  ∀ {env : Environment} {X : Name}, chk9 0 env X = true → X = hftRoot ∧ RootReader lvl₀ env NmHttp HttpData ∧ RootReader lvl₀ env NmTlp TlpData

/-- the bridge `RootReader → ReaderAt`, written again -/
noncomputable def Br_real : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d : MachineData}, RootReader lvl env X d → Tools.ShippingFGCircuitFinal4.ReaderAt lvl env X d
noncomputable def BrMu_reverse : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d : MachineData}, Tools.ShippingFGCircuitFinal4.ReaderAt lvl env X d → RootReader lvl env X d
noncomputable def BrMu_lvl : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d : MachineData}, RootReader lvl env X d → Tools.ShippingFGCircuitFinal4.ReaderAt lvlSucc env X d
noncomputable def BrMu_env : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d : MachineData}, RootReader lvl env X d → Tools.ShippingFGCircuitFinal4.ReaderAt lvl (envX env) X d
noncomputable def BrMu_data : Prop :=
  ∀ {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d d' : MachineData}, RootReader lvl env X d → Tools.ShippingFGCircuitFinal4.ReaderAt lvl env X d'

def unfold48 : List Name := [``Tools.ShippingFGCircuitS3f2Final.HftFinalStmtOffCombined9, ``Tools.ShippingFGCircuitS3f2Final.pilotReaderOk2, ``Tools.ShippingFGCircuitS3dFinal.HftFinalStmtOffCombined8, ``Tools.ShippingFGCircuitS3cFinal.HftFinalStmtOffCombined7,
  ``Tools.ShippingFGCircuitS3b2Final.HftFinalStmtOffCombined7R, ``Tools.ShippingFGCircuitS3aFinal.HftFinalStmtOffCombined6,
  ``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT, ``Tools.ShippingFGCircuitS2mReach.TeleRX, ``Tools.ShippingFGCircuitS2mReach.quietRX]
/-- the ONE normalisation path of this Check, as in Check47 (`normC`), plus the unfolding of the new checker and statement -/
def norm48 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold48.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  normC e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck48 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- the complete type of v9
  let f9ty ← tyOf ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9
  let f9 ← norm48 f9ty
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined9" f9 (← norm48 (Q "F9_real"))
  for mu in ["F9Mu_noStart", "F9Mu_noRun", "F9Mu_noCell", "F9Mu_noD", "F9Mu_noG", "F9Mu_noT", "F9Mu_noPS", "F9Mu_noProf",
      "F9Mu_entV8", "F9Mu_entOff", "F9Mu_entTrue", "F9Mu_entNoReader", "F9Mu_entNoGates", "F9Mu_entNoRootDef", "F9Mu_entNoChildren", "F9Mu_entRootLvl", "F9Mu_entRootData",
      "F9Mu_root", "F9Mu_postRoot", "F9Mu_startCtx", "F9Mu_startWorld", "F9Mu_reachEnd", "F9Mu_reachOther", "F9Mu_conEnd", "F9Mu_conOther",
      "F9Mu_teleV6", "F9Mu_teleOrigPlain", "F9Mu_teleOrigX", "F9Mu_teleAdmStrong", "F9Mu_teleNoReach", "F9Mu_teleNoReads",
      "F9Mu_lvlGPt0", "F9Mu_lvlGPtSucc", "F9Mu_outModule", "F9Mu_outDesign", "F9Mu_outBoth", "F9Mu_artHttp", "F9Mu_noC1", "F9Mu_noC2", "F9Mu_carrierZ", "F9Mu_carrierOld",
      "F9Mu_hchkBack", "F9Mu_hchkBackLvl", "F9Mu_hchkBackStartEnv", "F9Mu_hchkBackEndEnv", "F9Mu_env0Back"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined9 vs {mu}" f9 (← norm48 (Q mu)); nm := nm + 1
  -- v9 is none of v6, v7, v7r, v8
  for (what, c) in [("v6", ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6), ("v7", ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7),
      ("v7r", ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R), ("v8", ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8)] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined9 vs the {what} theorem's type" f9 (← norm48 (← tyOf c)); nm := nm + 1
  -- soundness of the check
  let sd ← norm48 (← tyOf ``Tools.ShippingFGCircuitS3f2Final.pilotReaderOk2_sound)
  Tests.Gen5.FGCircuitCmp.checkSame "pilotReaderOk2_sound" sd (← norm48 (Q "Snd2_real"))
  let mut nmS : Nat := 0
  for mu in ["Snd2Mu_true", "Snd2Mu_v8chk", "Snd2Mu_envCheck", "Snd2Mu_envChildren", "Snd2Mu_envRoot", "Snd2Mu_lvlChildren", "Snd2Mu_lvlRoot0", "Snd2Mu_lvlRootSucc",
      "Snd2Mu_rootName", "Snd2Mu_rootType", "Snd2Mu_rootValue", "Snd2Mu_rootData", "Snd2Mu_swapChildren", "Snd2Mu_noRoot", "Snd2Mu_noCheckedEnv"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"pilotReaderOk2_sound vs {mu}" sd (← norm48 (Q mu)); nmS := nmS + 1
  -- the bridge RootReader -> ReaderAt
  let br ← norm48 (← tyOf ``Tools.ShippingFGCircuitS3f2Final.readerAt_of_rootReader)
  Tests.Gen5.FGCircuitCmp.checkSame "readerAt_of_rootReader" br (← norm48 (Q "Br_real"))
  for mu in ["BrMu_reverse", "BrMu_lvl", "BrMu_env", "BrMu_data"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"readerAt_of_rootReader vs {mu}" br (← norm48 (Q mu)); nmS := nmS + 1
  -- binder lists
  let bl (t : Lean.Expr) : MetaM (List Name) := do return binderNames ((← unfoldDefinition? t).getD t)
  let b8 ← bl (← tyOf ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8)
  let b9 ← bl f9ty
  unless b9 == b8.filter (fun n => n != `env₀ && n != `hchk) do throwError "v9 is not v8 minus [env₀, hchk]: v8 {b8}, v9 {b9}"
  unless b8.length == 20 && b9.length == 18 do throwError "binder counts: v8 {b8.length}, v9 {b9.length}"
  unless b9 == [`ι, `mref, `cref, `L, `mctx, `cctx, `w, `w', `b, `D', `hstart, `hr, `hcell, `hD, `hG, `hT, `hs, `h0] do
    throwError "v9 binders are not L hstart hr hcell hD hG hT hs h0: {b9}"
  for n in [`env₀, `hchk, `hadm, `hdown, `lvl, `hreadH, `hreadT] do
    unless !b9.contains n do throwError "v9 still has {n}"
  logInfo m!"FGCIRCUIT48 BINDERS (9 implicit + explicit): v8 ({b8.length} = 9 + 11) {b8}; v9 ({b9.length} = 9 + 9) {b9}; v9 = v8 minus [env₀, hchk]; explicit binders L hstart hr hcell hD hG hT hs h0"
  logInfo m!"FGCIRCUIT48 SIGNATURES: the complete type of synth_hftPcieOutByte_finalOffCombined9 equals the independently written Exp9 under ONE criterion (FGCircuitCmp.stmtEq after the ONE normalisation function norm48 = Check47.normC applied to the real type, the expected statement and every mutant); {nm} mutants rejected (each premise dropped; entry = v8's pilotReaderOk / ordinary Off / True checker / the checker without its root reader, without gates, without the root definition, without the children, with the root reader at another level or against another machineData; other root / post-run root; start context / world not the run's; reach and conclusion at the end / another environment; hT: the old TeleR, the original quiet's law alone (plain and X form), the context from the strengthened quiet, no reach, no ReadsAt; GPt at another level; another Module / Design / artifact name; weakened conclusion; carriers cdvZ and cdvOld; env₀ and hchk back (at the start / end environment, at another level), env₀ alone back; v6, v7, v7r, v8); pilotReaderOk2_sound against ExpSnd2 and readerAt_of_rootReader against the independently written bridge: {nmS} further mutants rejected (True checker, v8's checker, the check / children / root at another environment, children / root at another level, root name / type / value / data, swapped children, no root equation, no CheckedEnv; reverse bridge, other level, other environment, other data)"

/-! ## A. controls of the checker on the real environment, and the output -/
run_cmd liftTermElabM do
  let env ← getEnv
  let ok (b : Bool) (msg : String) : MetaM Unit := unless b do throwError "FGCIRCUIT48 control failed: {msg}"
  let some (.defnInfo d) := env.find? hftRoot | throwError "the real environment has no root"
  -- the real environment passes, as a whole and by conjunct
  ok (pilotReaderOk2 env hftRoot) "real environment: true"
  ok (rootDefB env hftRoot hftRootType hftRootValue) "root definition true"
  ok (entryGatesB env hftRoot) "gates true"
  ok (rootReaderB lvl₀ env hftRoot rootMD) "root reader true"
  -- root name: another declaration, a child as the root, a missing constant
  ok (!pilotReaderOk2 env `Some.Other.Decl) "another root name"
  ok (!pilotReaderOk2 env hftHttp) "the child as root"
  ok (!rootDefB env hftHttp hftRootType hftRootValue) "root definition: another name"
  ok (!rootDefB env `Sparkle.NoSuchConstant hftRootType hftRootValue) "root definition: missing constant"
  ok (!rootReaderB lvl₀ env `Sparkle.NoSuchConstant rootMD) "root reader: missing constant"
  -- root type / value: altered; swapped; a level parameter; not a definition
  ok (!rootDefB env hftRoot (.bvar 0) hftRootValue) "root type altered"
  ok (!rootDefB env hftRoot hftRootValue hftRootValue) "root type = the value"
  ok (!rootDefB env hftRoot hftRootType (.bvar 0)) "root value altered"
  ok (!rootDefB env hftRoot hftRootType hftRootType) "root value = the type"
  let tyAlt := match hftRootType with | .forallE n t b bi => Lean.Expr.forallE n t (.bvar 7) bi | e => e
  let valAlt := match hftRootValue with | .lam n t b bi => Lean.Expr.lam n t (.bvar 7) bi | e => e
  ok (!(tyAlt == hftRootType)) "the altered type differs"
  ok (!rootDefB env hftRoot tyAlt hftRootValue) "root type: one nested subterm altered"
  ok (!rootDefB env hftRoot hftRootType valAlt) "root value: one nested subterm altered"
  let addAs (nm : Name) (f : DefinitionVal → DefinitionVal) : MetaM Environment := do
    match env.addDeclCore 0 (.defnDecl (f { d with name := nm })) none false with
    | .ok e => pure e
    | .error _ => throwError "could not add {nm}"
  let envLp ← addAs `Test.rootLp (fun d => { d with levelParams := [`u] })
  ok (rootDefB envLp `Test.rootLp d.type d.value == false) "root with a level parameter: false"
  let envOk ← addAs `Test.rootCopy id
  ok (rootDefB envOk `Test.rootCopy hftRootType hftRootValue) "a copy of the root under another name with the real type and value: true (the control for the three above)"
  let envTy ← addAs `Test.rootTy (fun d => { d with type := tyAlt })
  ok (!rootDefB envTy `Test.rootTy hftRootType hftRootValue) "added root with an altered type"
  let envVal ← addAs `Test.rootVal (fun d => { d with value := valAlt })
  ok (!rootDefB envVal `Test.rootVal hftRootType hftRootValue) "added root with an altered value"
  let envThm ← match env.addDeclCore 0 (.thmDecl { name := `Test.rootThm, levelParams := [], type := d.type, value := d.value }) none false with
    | .ok e => pure e | .error _ => throwError "could not add a theorem"
  ok (!rootDefB envThm `Test.rootThm hftRootType hftRootValue) "a theorem is not the root definition"
  -- gates: a declaration the certified front end accepts (a Bool gate `fun a => a`) has gates FALSE; the real root's are true; the checker's gate conjunct is that same function
  let sig (dom t : Lean.Expr) : Lean.Expr := .app (.app (.const ``Sparkle.Core.Signal.Signal [Level.zero]) dom) t
  let dd := Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain []
  let bool := Lean.Expr.const ``Bool []
  let gTy : Lean.Expr := Lean.Expr.forallE `a (sig dd bool) (sig dd bool) BinderInfo.default
  let gVal : Lean.Expr := Lean.Expr.lam `a (sig dd bool) (Lean.Expr.bvar 0) BinderInfo.default
  let gDecl : Declaration := Declaration.defnDecl { name := `Test.gateId, levelParams := [], type := gTy, value := gVal, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let envG ← match env.addDeclCore 0 gDecl none false with
    | .ok e => pure e | .error _ => throwError "could not add the gate declaration"
  ok (!(entryGatesB envG `Test.gateId)) "gates: a certified-shape declaration has gates false"
  ok (entryGatesB envG hftRoot) "gates: the real root's gates stay true in the extended environment"
  -- reader: data altered in each component of the comparison, other children's data, another level
  let m := rootMD
  ok (!rootReaderB lvl₀ env hftRoot Tools.ShippingFGCircuitS3b2Exp.httpMD) "root reader against the HTTP child's data"
  ok (!rootReaderB lvl₀ env hftRoot Tools.ShippingFGCircuitS3b2Exp.tlpMD) "root reader against the TLP child's data"
  ok (!rootReaderB lvl₀ env hftHttp rootMD) "HTTP child against the root's data"
  ok (!rootReaderB lvl₀ env hftRoot { m with nIn := m.nIn + 1 }) "root data: nIn altered"
  ok (!rootReaderB lvl₀ env hftRoot { m with dom := mkNatLit 0 }) "root data: dom altered"
  ok (!rootReaderB lvl₀ env hftRoot { m with bposL := 0 :: m.bposL }) "root data: bposL altered"
  ok (!rootReaderB lvl₀ env hftRoot { m with vwL := m.vwL.reverse ++ [1] }) "root data: vwL altered"
  ok (!rootReaderB lvl₀ env hftRoot { m with ls := m.ls ++ m.ls }) "root data: ls doubled"
  ok (!rootReaderB lvl₀ env hftRoot { m with outs := m.outs.reverse ++ m.outs }) "root data: outs altered"
  ok (!rootReaderB lvl₀ env hftRoot { m with shape := { m.shape with body := mkNatLit 0 } }) "root data: shape.body altered"
  ok (!rootReaderB lvl₀ env hftRoot { m with shape := { m.shape with binders := m.shape.binders.reverse } }) "root data: shape.binders reversed"
  ok (mdBeq m m) "mdBeq reflexive on the root's data"
  let lvOk (k : Nat) : Bool := rootReaderB (fun _ => k) env hftRoot rootMD
  -- the start environment: another environment (only `Init` imported) and the environment with the root's definition altered (the added copies above)
  let env' ← importModules #[{ module := `Init }] {} (loadExts := false)
  ok (!pilotReaderOk2 env' hftRoot) "Init-only environment: false"
  ok (!rootDefB env' hftRoot hftRootType hftRootValue) "Init-only environment, root definition: false"
  ok (!rootReaderB lvl₀ env' hftRoot rootMD) "Init-only environment, root reader: false"
  ok (entryGatesB env' hftRoot) "Init-only environment: the gates pass on a missing constant (as EntryGates), the other conjuncts refuse it"
  -- the kernel equation of the executable copy (the typed check is `rootMD_eq`; here the printed pieces agree)
  logInfo m!"FGCIRCUIT48 CONTROLS: ok (real environment true as a whole and by conjunct; other root name / child as root / missing constant; root type / value altered, swapped, one nested subterm altered; gates false for a certified-shape declaration, true for the root; a level parameter, a theorem, a copy under another name true; root data altered in 8 components, another machineData, another name; Init-only environment false); the root reader at constant levels 0, 1, 3, 10 and lvl₀ gives {[lvOk 0, lvOk 1, lvOk 3, lvOk 10]} + true (the Bool check does not tell levels apart, as for the children in Check46r; the certified level is a property of the statement, SIGNATURES)"

run_cmd liftTermElabM do
  let X := hftRoot
  let (m1, d1, v1) ← Tools.ShippingFGCircuitS3f2Final.pilotArtifact2 X
  let (m2, d2) ← Sparkle.Compiler.Elab.synthesizeCombinationalOff X
  let (m0, d0, v0) ← Tools.ShippingFGCircuitS3b2Final.pilotArtifact X
  let rp (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) : String := toString (repr m) ++ "\n" ++ toString (repr d)
  unless rp m1 d1 == rp m2 d2 do throwError "FGCIRCUIT48 OUTPUT: the new pilot entry and the existing Off entry differ"
  unless rp m1 d1 == rp m0 d0 do throwError "FGCIRCUIT48 OUTPUT: the new pilot entry and the pilotReaderOk entry differ"
  unless v1 == Sparkle.Compiler.Elab.verilogOf m2 do throwError "FGCIRCUIT48 OUTPUT: the text printed from the new entry's run differs from the existing entry's"
  unless v1 == v0 do throwError "FGCIRCUIT48 OUTPUT: the printed text differs from the pilotReaderOk entry's"
  -- negative controls of the comparison: another artifact, an altered returned Module
  let (mH, dH) ← Sparkle.Compiler.Elab.synthesizeCombinationalOff hftHttp
  unless rp mH dH != rp m1 d1 do throwError "FGCIRCUIT48 OUTPUT control: another declaration's artifact compares equal"
  unless rp { m1 with name := m1.name ++ "x" } d1 != rp m2 d2 do throwError "FGCIRCUIT48 OUTPUT control: an altered Module compares equal"
  unless rp m1 { d1 with modules := [] } != rp m2 d2 do throwError "FGCIRCUIT48 OUTPUT control: an altered Design compares equal"
  unless Sparkle.Compiler.Elab.verilogOf { m1 with name := m1.name ++ "x" } != v1 do throwError "FGCIRCUIT48 OUTPUT control: an altered Module prints the same text"
  -- the explicit errors: another declaration, a false check
  let msg ← try
      discard <| Tools.ShippingFGCircuitS3f2Final.pilotEntry2 hftHttp
      pure "NO ERROR"
    catch e => e.toMessageData.toString
  unless msg.contains "reader check" do throwError "FGCIRCUIT48 ERROR control (another declaration): {msg}"
  logInfo m!"FGCIRCUIT48 OUTPUT: module+design repr of the new pilot entry = the existing Off entry = the pilotReaderOk entry ({(toString (repr m1)).length} / {(toString (repr d1)).length} chars); the Verilog text printed from the new run's own Module is identical ({v1.length} chars); controls: another declaration's artifact, an altered Module name, an altered Design all compare unequal; another declaration is refused with the reader-check error (no fallback)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3f2Exp.rootMD_eq, ``Tools.ShippingFGCircuitS3f2Final.rootDefB_sound, ``Tools.ShippingFGCircuitS3f2Final.readerAt_of_rootReader,
    ``Tools.ShippingFGCircuitS3f2Final.pilotReaderOk2_sound, ``Tools.ShippingFGCircuitS3f2Final.synth_hftPcieOutByte_finalOffCombined9,
    ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT48 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck48
