import Tools.ShippingFGCircuitS3dFinal
import Tests.Gen5.FGCircuitPilotCheck46
import Tests.Gen5.FGCircuitPilotCheck46r
set_option autoImplicit false
-- FG circuit pilot Check47 (S3d, S3e, S3e repair): the complete type of v8 (pilot entry, lvl₀, hadm/hdown/lvl/hreadH/hreadT removed, hT at TeleRX) against an independently written statement (Exp8; hT is written out again in this file (ExpTXind / ExpQuietX), not via Check46.ExpTX / quietRX / Laws.toX. SUPERSEDED: the earlier wording of this comment, \"the only reuse is Check46.ExpTX, unavoidable\" (draft a95cfacb), is out of date. S3e repair: the real type, F8_real and every mutant now go through ONE normalisation function, normC), mutants (each premise dropped; entry = True checker / ordinary Off run / another root; start world / context not the run's; TeleR instead of TeleRX; hadm/hdown/lvl/readers back; other level in hchk or GPt; weakened / other conclusion; other carrier), a binder-list comparison with v6, v7 and v7r, and standard axioms only.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck47
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

/-- the strengthened quiet predicate of the X form, written out here (NOT `quietRX`): quiet, the Core environment reads as `e`, reached from `w₀` by leaf steps of the context predicate `adm` -/
def ExpQuietX (quiet : W → Prop) (adm : CtxPred) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) : W → Prop :=
  fun w => quiet w ∧ ReadsAt e cref w ∧ ReachedX quiet adm mref cref w₀ w

/-- **hT, written again, independent of `quietRX` / `Laws.toX` / `Check46.ExpTX`.** `k = 0` is the TeleRX proposition of v8: the telescope law `RefLawsATeleX` at the strengthened quiet predicate (`ExpQuietX` over `L.O.quiet`, with the context predicate `AdmCtx L.O.quiet`) and the context predicate `AdmCtx L.O.quiet` (the admissibility of `L.O`, spelled out separately from the strengthened quiet). The mutants: 1 = the old `TeleR` (`RefLawsATele`, strengthened quiet via the plain `Reached`); 2 = the original quiet alone, plain law (`L.T`'s type, `RefLawsATele L.O.quiet`); 3 = the original quiet alone in the X form (`L.T.toX`'s type, `RefLawsATeleX L.O.quiet (AdmCtx L.O.quiet)`); 4 = the strengthened quiet with the context predicate made from the strengthened quiet (`AdmCtx` of it); 5 = strengthened quiet without the reach; 6 = strengthened quiet without `ReadsAt`. -/
def ExpTXind {mref : Rf1} {cref : Rf2} (L : Laws mref cref) (e : Environment) (w₀ : W) (k : Nat) : Prop :=
  if k == 0 then RefLawsATeleX (ExpQuietX L.O.quiet (AdmCtx L.O.quiet) mref cref e w₀) (AdmCtx L.O.quiet) mref cref
  else if k == 1 then ExpT L.O e w₀
  else if k == 2 then RefLawsATele L.O.quiet mref cref
  else if k == 3 then RefLawsATeleX L.O.quiet (AdmCtx L.O.quiet) mref cref
  else if k == 4 then RefLawsATeleX (ExpQuietX L.O.quiet (AdmCtx L.O.quiet) mref cref e w₀) (AdmCtx (ExpQuietX L.O.quiet (AdmCtx L.O.quiet) mref cref e w₀)) mref cref
  else if k == 5 then RefLawsATeleX (fun w => L.O.quiet w ∧ ReadsAt e cref w) (AdmCtx L.O.quiet) mref cref
  else RefLawsATeleX (fun w => L.O.quiet w ∧ ReachedX L.O.quiet (AdmCtx L.O.quiet) mref cref w₀ w) (AdmCtx L.O.quiet) mref cref

/-- the reader checks of the entry: 0 = the pilot's; 1 = always true; 3 = the two children's data swapped; 4 = the two children's names swapped; 5 = the HTTP child read at another level; 6 = the TLP child read at another level; 7 = the root equation dropped -/
def chkOf (ent : Nat) : Environment → Name → Bool :=
  if ent == 1 then (fun _ _ => true)
  else if ent == 3 then (fun env X => X == hftRoot && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftHttp Tools.ShippingFGCircuitS3b2Exp.tlpMD && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftTlp Tools.ShippingFGCircuitS3b2Exp.httpMD)
  else if ent == 4 then (fun env X => X == hftRoot && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftTlp Tools.ShippingFGCircuitS3b2Exp.httpMD && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftHttp Tools.ShippingFGCircuitS3b2Exp.tlpMD)
  else if ent == 5 then (fun env X => X == hftRoot && Tools.ShippingFGCircuitS3b2Reader.rootReaderB lvlSucc env hftHttp Tools.ShippingFGCircuitS3b2Exp.httpMD && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftTlp Tools.ShippingFGCircuitS3b2Exp.tlpMD)
  else if ent == 6 then (fun env X => X == hftRoot && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftHttp Tools.ShippingFGCircuitS3b2Exp.httpMD && Tools.ShippingFGCircuitS3b2Reader.rootReaderB lvlSucc env hftTlp Tools.ShippingFGCircuitS3b2Exp.tlpMD)
  else if ent == 7 then (fun env _ => Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftHttp Tools.ShippingFGCircuitS3b2Exp.httpMD && Tools.ShippingFGCircuitS3b2Reader.rootReaderB Tools.ShippingFGCircuitS3b2Reader.lvl₀ env hftTlp Tools.ShippingFGCircuitS3b2Exp.tlpMD)
  else Tools.ShippingFGCircuitS3b2Final.pilotReaderOk

/-- the Module / Design the conclusion speaks about: `k` = 0 the run's, 1 another Module (renamed), 2 another Design (no modules), 3 both -/
def modOf (k : Nat) (b : Mod) : Mod := if k == 1 then { b with name := b.name ++ "x" } else if k == 3 then { b with name := b.name ++ "x" } else b
def desOf (k : Nat) (D : Design) : Design := if k == 2 then { D with modules := [] } else if k == 3 then { D with modules := [] } else D

/-- **v8, written again.** Knobs: the premises (Bool); `ent` = the run's entry (0 = `synthesizeCombinationalOffR pilotReaderOk root`; 1, 3-7 = the same with another reader check (`chkOf`); 2 = the ordinary Off entry `synthesizeCombinationalOff`); `st` = the start premise (0 = `Start L mctx cctx w`, 1 = some other context, 2 = some other world); `tele` (`ExpTXind`: 0 = TeleRX, others the mutants); the old premises `hadm`/`hdown`, the two child readers back as premises (`readers`, variant `rdv`: 0 = as the root's, 2 = names swapped, 3 = HTTP at another level, 4 = TLP at another level); the levels of `hchk` / `GPt`; the environment of `hchk` (`chkE`, 0 = `env₀`) and of the conclusion (`conE`); the reach environment, root, post-run root, artifact name; conclusion parts; the Module / Design (`outM`); carrier. -/
noncomputable def Exp8 (nStart nRun nCell nChk nD nG nT nPS nProf : Bool) (ent st tele : Nat) (addAdm addDown readers : Bool) (rdv : Nat)
    (lvC lvG : Lean.Expr → Nat) (c1 c2 : Bool) (eA chkE conE : EnvK) (root postRoot art : Name) (outM : Nat) (CV : CDRel) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Pre nStart (if st == 0 then Start L mctx cctx w else if st == 1 then (∃ mctx2 : Cx, Start L mctx2 cctx w) else (∃ w2 : W, Start L mctx cctx w2)) (
    Pre nRun (RunsTo (if ent == 2 then synthesizeCombinationalOff root else synthesizeCombinationalOffR (chkOf ent) root) mctx mref cctx cref w (b, D') w') (
    Pre nCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    Pre nChk (CheckedStart lvC (chkE cref w w' env₀) cref w root hftRootType hftRootValue RootData) (
    Pre readers (RootReader (if rdv == 3 then lvlSucc else lvC) (envAt cref w) (if rdv == 2 then NmTlp else NmHttp) HttpData) (
    Pre readers (RootReader (if rdv == 4 then lvlSucc else lvC) (envAt cref w) (if rdv == 2 then NmHttp else NmTlp) TlpData) (
    Pre addAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (eA cref w w' env₀) w) mctx cctx) (
    Pre addDown (ExpDown L.O (eA cref w w' env₀) w) (
    Pre nD (ExpD L.O (eA cref w w' env₀) w) (
    Pre nG (ExpG L.O (eA cref w w' env₀) w) (
    Pre nT (ExpTXind L (eA cref w w' env₀) w tele) (
    Pre nPS (ExpPS L.O w) (
    Pre nProf (ExpProfOff mref cref w) (
    (if c1 then (∃ raw, PostRunOff mctx mref cctx cref w postRoot (desOf outM D') (modOf outM b) raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (conE cref w w' env₀) (GPt (ι := ι) lvG (conE cref w w' env₀)) (PostRunOff mctx mref cctx cref w postRoot (desOf outM D')) art shHft mm (modOf outM b) (desOf outM D') p) else True))))))))))))))

noncomputable def F8 (nStart nRun nCell nChk nD nG nT nPS nProf : Bool := true) (ent st tele : Nat := 0) (addAdm addDown readers : Bool := false) (rdv : Nat := 0)
    (lvC lvG : Lean.Expr → Nat := Tools.ShippingFGCircuitS3b2Reader.lvl₀) (c1 c2 : Bool := true)
    (eA : EnvK := eS) (chkE : EnvK := e0) (conE : EnvK := eS) (root postRoot art : Name := NmRoot) (outM : Nat := 0) (CV : CDRel := CVT) : Prop :=
  Exp8 nStart nRun nCell nChk nD nG nT nPS nProf ent st tele addAdm addDown readers rdv lvC lvG c1 c2 eA chkE conE root postRoot art outM CV

noncomputable def F8_real : Prop := F8
noncomputable def F8Mu_noStart : Prop := F8 (nStart := false)
noncomputable def F8Mu_noRun : Prop := F8 (nRun := false)
noncomputable def F8Mu_noCell : Prop := F8 (nCell := false)
noncomputable def F8Mu_noChk : Prop := F8 (nChk := false)
noncomputable def F8Mu_noD : Prop := F8 (nD := false)
noncomputable def F8Mu_noG : Prop := F8 (nG := false)
noncomputable def F8Mu_noT : Prop := F8 (nT := false)
noncomputable def F8Mu_noPS : Prop := F8 (nPS := false)
noncomputable def F8Mu_noProf : Prop := F8 (nProf := false)
-- the entry: another reader (True checker), the ordinary Off run, another root
noncomputable def F8Mu_entTrue : Prop := F8 (ent := 1)
noncomputable def F8Mu_entOff : Prop := F8 (ent := 2)
noncomputable def F8Mu_root : Prop := F8 (root := NmHttpX)
noncomputable def F8Mu_postRoot : Prop := F8 (postRoot := NmHttpX)
-- the child readers (the entry's check): data swapped, names swapped, one child at another level, no root equation
noncomputable def F8Mu_entSwapData : Prop := F8 (ent := 3)
noncomputable def F8Mu_entSwapName : Prop := F8 (ent := 4)
noncomputable def F8Mu_entHttpLvl : Prop := F8 (ent := 5)
noncomputable def F8Mu_entTlpLvl : Prop := F8 (ent := 6)
noncomputable def F8Mu_entNoRoot : Prop := F8 (ent := 7)
-- the start world / context are the run's
noncomputable def F8Mu_startCtx : Prop := F8 (st := 1)
noncomputable def F8Mu_startWorld : Prop := F8 (st := 2)
-- the start environment: `hchk` at the run's start environment / the run's end environment; the conclusion at env₀ / the end environment
noncomputable def F8Mu_chkEnvStart : Prop := F8 (chkE := eS)
noncomputable def F8Mu_chkEnvEnd : Prop := F8 (chkE := eE)
noncomputable def F8Mu_conEnv0 : Prop := F8 (conE := e0)
noncomputable def F8Mu_conEnvEnd : Prop := F8 (conE := eE)
-- hT: the old TeleR; the original quiet's law alone (plain and X form); other contexts / quiet predicates
noncomputable def F8Mu_teleV6 : Prop := F8 (tele := 1)
noncomputable def F8Mu_teleOrigPlain : Prop := F8 (tele := 2)
noncomputable def F8Mu_teleOrigX : Prop := F8 (tele := 3)
noncomputable def F8Mu_teleAdmStrong : Prop := F8 (tele := 4)
noncomputable def F8Mu_teleNoReach : Prop := F8 (tele := 5)
noncomputable def F8Mu_teleNoReads : Prop := F8 (tele := 6)
noncomputable def F8Mu_reachEnd : Prop := F8 (eA := eE)
noncomputable def F8Mu_reachEnv0 : Prop := F8 (eA := e0)
-- the removed premises back
noncomputable def F8Mu_addAdm : Prop := F8 (addAdm := true)
noncomputable def F8Mu_addDown : Prop := F8 (addDown := true)
noncomputable def F8Mu_addBoth : Prop := F8 (addAdm := true) (addDown := true)
noncomputable def F8Mu_readersBack : Prop := F8 (readers := true)
noncomputable def F8Mu_readersSwapName : Prop := F8 (readers := true) (rdv := 2)
noncomputable def F8Mu_readersHttpLvl : Prop := F8 (readers := true) (rdv := 3)
noncomputable def F8Mu_readersTlpLvl : Prop := F8 (readers := true) (rdv := 4)
-- the level: other level in hchk / in GPt
noncomputable def F8Mu_lvlChk0 : Prop := F8 (lvC := lvlZero)
noncomputable def F8Mu_lvlChkSucc : Prop := F8 (lvC := lvlSucc)
noncomputable def F8Mu_lvlGPt0 : Prop := F8 (lvG := lvlZero)
noncomputable def F8Mu_lvlGPtSucc : Prop := F8 (lvG := lvlSucc)
-- the output: a conclusion about another Module / Design than the run returned; another artifact name
noncomputable def F8Mu_outModule : Prop := F8 (outM := 1)
noncomputable def F8Mu_outDesign : Prop := F8 (outM := 2)
noncomputable def F8Mu_outBoth : Prop := F8 (outM := 3)
noncomputable def F8Mu_artHttp : Prop := F8 (art := NmHttp)
noncomputable def F8Mu_artHttpX : Prop := F8 (art := NmHttpX)
-- the conclusion: weakened; the carrier
noncomputable def F8Mu_noC1 : Prop := F8 (c1 := false)
noncomputable def F8Mu_noC2 : Prop := F8 (c2 := false)
noncomputable def F8Mu_carrierZ : Prop := F8 (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)
noncomputable def F8Mu_carrierOld : Prop := F8 (CV := Tools.ShippingFGCircuitS1tFinal.cdvOld)

def unfold47 : List Name := [``Tools.ShippingFGCircuitS3dFinal.HftFinalStmtOffCombined8, ``Tools.ShippingFGCircuitS3cFinal.HftFinalStmtOffCombined7,
  ``Tools.ShippingFGCircuitS3b2Final.HftFinalStmtOffCombined7R, ``Tools.ShippingFGCircuitS3aFinal.HftFinalStmtOffCombined6,
  ``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT, ``Tools.ShippingFGCircuitS2mReach.TeleRX, ``Tools.ShippingFGCircuitS2mReach.quietRX]
/-- the structure builders `Laws.toX` / `RefLawsAOps.toX`: a projection of one is read off its definition (`L.toX.O.quiet` is `L.O.quiet`, `L.toX.O.adm` is `AdmCtx L.O.quiet`), on the real type and on every expected statement alike -/
def toXNames : List Name := [``Tools.ShippingGen2.Laws.toX, ``Tools.ShippingChildInvA.RefLawsAOps.toX]
partial def projToX (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some (sName, idx, s, rest) := (← do
    match e.getAppFn with
    | .proj sn i s => pure (some (sn, i, s, e.getAppArgs))
    | .const c _ =>
      match ← getProjectionFnInfo? c with
      | some info =>
        if !info.fromClass && e.getAppNumArgs > info.numParams then
          let args := e.getAppArgs
          let ctor ← getConstInfoCtor info.ctorName
          pure (some (ctor.induct, info.i, args[info.numParams]!, args.extract (info.numParams + 1) args.size))
        else pure none
      | none => pure none
    | _ => pure none) | return none
  let sh := s.getAppFn
  let isToX : Bool := match sh with | .const c _ => toXNames.contains c | _ => false
  unless isToX do return none
  let s' ← withTransparency .all (whnf s)
  unless s'.getAppFn.isConst do return none
  let r ← whnfCore (mkAppN (Lean.Expr.proj sName idx s'.headBeta) rest)
  return some r
def norm47 (e0 : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e0
  for _ in [0:3] do
   e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some r ← projToX e then return .visit r
    if let .const c _ := e.getAppFn then
      if unfold47.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e
/-- the ONE normalisation path of this Check: `norm47` (projToX, unfold the statement wrappers, `norm37`), then `norm47` again so that the `toX` projections exposed by the unfolding are read off as well. The real type, the expected `F8_real` and every mutant go through exactly this function. -/
def normC (e : Lean.Expr) : MetaM Lean.Expr := do norm47 (← norm47 e)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck47 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  let f8ty ← tyOf ``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8
  let f8 ← normC f8ty
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined8" f8 (← normC (Q "F8_real"))
  for mu in ["F8Mu_noStart", "F8Mu_noRun", "F8Mu_noCell", "F8Mu_noChk", "F8Mu_noD", "F8Mu_noG", "F8Mu_noT", "F8Mu_noPS",
      "F8Mu_noProf", "F8Mu_entTrue", "F8Mu_entOff", "F8Mu_root", "F8Mu_postRoot", "F8Mu_entSwapData", "F8Mu_entSwapName", "F8Mu_entHttpLvl",
      "F8Mu_entTlpLvl", "F8Mu_entNoRoot", "F8Mu_startCtx", "F8Mu_startWorld", "F8Mu_chkEnvStart", "F8Mu_chkEnvEnd", "F8Mu_conEnv0", "F8Mu_conEnvEnd",
      "F8Mu_teleV6", "F8Mu_teleOrigPlain", "F8Mu_teleOrigX", "F8Mu_teleAdmStrong", "F8Mu_teleNoReach", "F8Mu_teleNoReads", "F8Mu_reachEnd", "F8Mu_reachEnv0",
      "F8Mu_addAdm", "F8Mu_addDown", "F8Mu_addBoth", "F8Mu_readersBack", "F8Mu_readersSwapName", "F8Mu_readersHttpLvl", "F8Mu_readersTlpLvl", "F8Mu_lvlChk0",
      "F8Mu_lvlChkSucc", "F8Mu_lvlGPt0", "F8Mu_lvlGPtSucc", "F8Mu_outModule", "F8Mu_outDesign", "F8Mu_outBoth", "F8Mu_artHttp", "F8Mu_artHttpX",
      "F8Mu_noC1", "F8Mu_noC2", "F8Mu_carrierZ", "F8Mu_carrierOld"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined8 vs {mu}" f8 (← normC (Q mu)); nm := nm + 1
  -- v8 is none of v6, v7, v7r
  let f6ty ← tyOf ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6
  let f7ty ← tyOf ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7
  let f7rty ← tyOf ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined8 vs the v6 theorem's type" f8 (← normC f6ty); nm := nm + 1
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined8 vs the v7 theorem's type" f8 (← normC f7ty); nm := nm + 1
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined8 vs the v7r theorem's type" f8 (← normC f7rty); nm := nm + 1
  -- binder lists
  let bl (t : Lean.Expr) : MetaM (List Name) := do return binderNames ((← unfoldDefinition? t).getD t)
  let b6 ← bl f6ty
  let b7 ← bl f7ty
  let b7r ← bl f7rty
  let b8 ← bl f8ty
  unless b8 == b7r.filter (fun n => n != `hadm && n != `hdown) do throwError "v8 is not v7r minus [hadm, hdown]: v7r {b7r}, v8 {b8}"
  unless b8 == b7.filter (fun n => n != `lvl && n != `hreadH && n != `hreadT) do throwError "v8 is not v7 minus [lvl, hreadH, hreadT]: v7 {b7}, v8 {b8}"
  unless b7r == b6.filter (fun n => n != `lvl && n != `hreadH && n != `hreadT) do throwError "v7r is not v6 minus [lvl, hreadH, hreadT]: v6 {b6}, v7r {b7r}"
  unless b6.length == 25 && b7.length == 23 && b7r.length == 22 && b8.length == 20 do
    throwError "binder counts: v6 {b6.length}, v7 {b7.length}, v7r {b7r.length}, v8 {b8.length}"
  for n in [`lvl, `hreadH, `hreadT, `hadm, `hdown] do
    unless !b8.contains n do throwError "v8 still has {n}"
  logInfo m!"FGCIRCUIT47 BINDERS (9 implicit + explicit): v6 ({b6.length} = 9 + 16) {b6}; v7 ({b7.length} = 9 + 14) {b7}; v7r ({b7r.length} = 9 + 13) {b7r}; v8 ({b8.length} = 9 + 11) {b8}; v8 = v7r minus [hadm, hdown] = v7 minus [lvl, hreadH, hreadT]; hT is stated at TeleRX (as v7), every other premise keeps its v6 proposition (docs S54)"
  logInfo m!"FGCIRCUIT47 SIGNATURES: the complete type of synth_hftPcieOutByte_finalOffCombined8 equals the independently written Exp8 under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths; hT is written out in Check47 itself (ExpTXind / ExpQuietX: adm = AdmCtx L.O.quiet and the strengthened quiet spelled separately, not via quietRX / Laws.toX / Check46.ExpTX; the real type, the expected F8_real and every mutant are all read through the SAME function normC = norm47 applied twice, i.e. the same projToX normalisation of L.toX also after the expected statement is unfolded)); {nm} mutants rejected (each premise dropped; True checker / ordinary Off run / other root / other post-run root; the entry's child reader check with the children's data swapped, names swapped, one child at another level, or no root equation; start context / world not the run's; hchk at the run's start / end environment; the conclusion at env₀ / the end environment; hT: the old TeleR, the original quiet's law alone (plain and X form), the context predicate from the strengthened quiet, no reach, no ReadsAt; hadm / hdown / both / the child readers back (also swapped / at another level); other level in hchk and in GPt; reach environment end / initial; a conclusion about another Module / Design / artifact name; weakened conclusion parts; carriers cdvZ and cdvOld; v6, v7, v7r)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3dFinal.synth_hftPcieOutByte_finalOffCombined8, ``Tools.ShippingFGCircuitS3cFinal.synth_hftPcieOutByte_finalOffCombined7,
    ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R, ``Tools.ShippingFGCircuitS3b2Final.pilotReaderOk_sound, ``Tools.ShippingFGCircuitS3b2Final.readerOk_of_run,
    ``Tools.ShippingFGCircuitS3b2Core.offR_to_off]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT47 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck47
