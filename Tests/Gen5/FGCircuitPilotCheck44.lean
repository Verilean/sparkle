import Tools.ShippingFGCircuitS2zFinal
import Tests.Gen5.FGCircuitPilotCheck43
set_option autoImplicit false
-- FG circuit pilot Check44 (S2z): A) controls of the environment check on the real environment; B) complete types (soundness, entry check, v5) against independently written statements, one criterion FGCircuitCmp.stmtEq. docs/FG-CIRCUIT-PILOT.md §49.
open Lean Elab Command Sparkle.Compiler.EnvTableCheck Tools.ShippingFGCircuitS2zEnvCheck Tools.ShippingFGCircuitS1mCD
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

run_cmd do
  let env ← getEnv
  let ok (b : Bool) (msg : String) : CommandElabM Unit := unless b do throwError "FGCIRCUIT44 control failed: {msg}"
  -- positive: the real environment (which contains the root) passes
  ok (env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot).isSome "root in env"
  ok (hftEnvCheckB env) "check true on the real environment"
  ok (defsOkB env (defTuples hftDeltaL)) "defs"
  ok (ctorsOkB env (ctorTuples hftGammaL)) "ctors"
  ok (recOkB env) "rec"
  let dl := defTuples hftDeltaL
  let gl := ctorTuples hftGammaL
  ok (dl.length == 55 && gl.length == 11) "table sizes 55/11"
  -- negative: one row altered, each field kind
  let some (c, lps, v) := dl.head? | throwError "empty defs"
  ok (!defsOkB env ((c, lps, mkNatLit 0) :: dl.tail)) "value altered"
  ok (!defsOkB env ((c, `u_alt :: lps, v) :: dl.tail)) "level params altered"
  ok (!defsOkB env ((`Sparkle.NoSuchConstant, lps, v) :: dl.tail)) "missing constant"
  ok (!defsOkB env ((dl.getLast!.1, dl.getLast!.2.1, mkNatLit 1) :: dl.dropLast.reverse).reverse) "last row value altered"
  let some (g, ind, np, nf) := gl.head? | throwError "empty ctors"
  ok (!ctorsOkB env ((g, ind, np, nf + 1) :: gl.tail)) "numFields altered"
  ok (!ctorsOkB env ((g, ind, np + 1, nf) :: gl.tail)) "numParams altered"
  ok (!ctorsOkB env ((g, `Sparkle.NoSuchInductive, np, nf) :: gl.tail)) "inductive altered"
  -- negative: a constant of the wrong kind (a def row naming a constructor, a ctor row naming a def)
  ok (!defsOkB env [(g, [], mkNatLit 0)]) "ctor named as def"
  ok (!ctorsOkB env [(c, ind, np, nf)]) "def named as ctor"
  -- negative: another environment (only `Init` imported): the Sparkle tables do not hold
  let env' ← importModules #[{ module := `Init }] {} (loadExts := false)
  ok (!hftEnvCheckB env') "check false on the Init-only environment"
  ok (recOkB env') "List.rec is in Init (the rec row alone passes there)"
  logInfo "FGCIRCUIT44 CONTROLS: ok (real env true; value/lps/missing/numFields/numParams/inductive/kind-swapped/Init-only false)"


/-! ## B. complete types against independently written statements (ONE criterion `FGCircuitCmp.stmtEq` for the expected statement and every mutant) -/
namespace Tests.Gen5.FGCircuitPilotCheck44
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1mCD (EnvDefs EnvCtors DefRow CtorRow)
open Tools.ShippingFGCircuitS1wTbl (RecFact)
open Tools.ShippingFGCircuitS2zEnvCheck (hftEnvCheckB)
open Sparkle.Compiler.PilotEnvTables (startEnvOk)
open Tools.ShippingFGCircuitS1kStmt (hftRoot)
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 EntryOf)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)
open Tests.Gen5.FGCircuitPilotCheck43 (FD4 Dl Gm)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)

noncomputable def envC : Environment := default
noncomputable def dropRow {α : Type} (T : Name → Option α) (c : Name) : Name → Option α := fun x => if x = c then none else T x
def NmMmio : Name := `Sparkle.IP.Bus.PCIe.mmioEndpoint
def NmHttpX : Name := `Tools.ShippingFGCircuitS1kRoot.synth_hftHttp

/-- the soundness statement, written again. Knobs: the checker, its result, the environment each condition speaks about, the tables, which conditions are concluded -/
noncomputable def ExpSnd (chk : Environment → Bool) (val : Bool) (e1 e2 e3 : Environment → Environment)
    (DT : Name → Option DefRow) (GT : Name → Option CtorRow) (n1 n2 n3 : Bool) : Prop :=
  ∀ (env : Environment), chk env = val →
    (if n1 then EnvDefs (e1 env) DT else True) ∧ (if n2 then EnvCtors (e2 env) GT else True) ∧ (if n3 then RecFact (e3 env) else True)

noncomputable def Snd (chk : Environment → Bool := hftEnvCheckB) (val : Bool := true) (e1 e2 e3 : Environment → Environment := id)
    (DT : Name → Option DefRow := Dl) (GT : Name → Option CtorRow := Gm) (n1 n2 n3 : Bool := true) : Prop := ExpSnd chk val e1 e2 e3 DT GT n1 n2 n3

/-- the entry check's soundness at the pilot root (written again) -/
noncomputable def ExpStart (X : Name) (val : Bool) (e1 e2 e3 : Environment → Environment) (DT : Name → Option DefRow) (GT : Name → Option CtorRow) (n1 n2 n3 : Bool) : Prop :=
  ∀ (env : Environment), startEnvOk X env = val →
    (if n1 then EnvDefs (e1 env) DT else True) ∧ (if n2 then EnvCtors (e2 env) GT else True) ∧ (if n3 then RecFact (e3 env) else True)

noncomputable def Strt (X : Name := hftRoot) (val : Bool := true) (e1 e2 e3 : Environment → Environment := id)
    (DT : Name → Option DefRow := Dl) (GT : Name → Option CtorRow := Gm) (n1 n2 n3 : Bool := true) : Prop := ExpStart X val e1 e2 e3 DT GT n1 n2 n3

/-- the run-level fact (written again): a run of the entry on `root` from `w` to `w'`, with the cell premise, passed the entry's check at `eA` -/
noncomputable def ExpRun (diag needCell : Bool) (root chkRoot : Name) (eA : EnvK) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tests.Gen5.FGCircuitPilotCheck26.Pre needCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w' →
    startEnvOk chkRoot (eA cref w w' envC) = true)

noncomputable def Run (diag noCell : Bool := false) (root : Name := hftRoot) (chkRoot : Name := hftRoot) (eA : EnvK := eS) : Prop := ExpRun diag (!noCell) root chkRoot eA

/-! mutants -/
noncomputable def Snd_real : Prop := Snd
noncomputable def SndMu_env1 : Prop := Snd (e1 := fun _ => envC)
noncomputable def SndMu_env2 : Prop := Snd (e2 := fun _ => envC)
noncomputable def SndMu_env3 : Prop := Snd (e3 := fun _ => envC)
noncomputable def SndMu_only1 : Prop := Snd (n2 := false) (n3 := false)
noncomputable def SndMu_only2 : Prop := Snd (n1 := false) (n3 := false)
noncomputable def SndMu_only3 : Prop := Snd (n1 := false) (n2 := false)
noncomputable def SndMu_no1 : Prop := Snd (n1 := false)
noncomputable def SndMu_no2 : Prop := Snd (n2 := false)
noncomputable def SndMu_no3 : Prop := Snd (n3 := false)
noncomputable def SndMu_none : Prop := Snd (n1 := false) (n2 := false) (n3 := false)
noncomputable def SndMu_dropDef : Prop := Snd (DT := dropRow Dl NmMmio)
noncomputable def SndMu_emptyDef : Prop := Snd (DT := fun _ => none)
noncomputable def SndMu_emptyCtor : Prop := Snd (GT := fun _ => none)
noncomputable def SndMu_false : Prop := Snd (val := false)
noncomputable def SndMu_recOnly : Prop := Snd (chk := fun env => Sparkle.Compiler.EnvTableCheck.recOkB env)
noncomputable def SndMu_defsOnly : Prop := Snd (chk := fun env => Sparkle.Compiler.EnvTableCheck.defsOkB env (Tools.ShippingFGCircuitS2zEnvCheck.defTuples Tools.ShippingFGCircuitS2zEnvCheck.hftDeltaL))

noncomputable def Strt_real : Prop := Strt
noncomputable def StrtMu_root : Prop := Strt (X := NmHttpX)
noncomputable def StrtMu_env1 : Prop := Strt (e1 := fun _ => envC)
noncomputable def StrtMu_env2 : Prop := Strt (e2 := fun _ => envC)
noncomputable def StrtMu_env3 : Prop := Strt (e3 := fun _ => envC)
noncomputable def StrtMu_only1 : Prop := Strt (n2 := false) (n3 := false)
noncomputable def StrtMu_no2 : Prop := Strt (n2 := false)
noncomputable def StrtMu_no3 : Prop := Strt (n3 := false)
noncomputable def StrtMu_dropDef : Prop := Strt (DT := dropRow Dl NmMmio)
noncomputable def StrtMu_false : Prop := Strt (val := false)

noncomputable def Run_real : Prop := Run
noncomputable def RunMu_end : Prop := Run (eA := eE)
noncomputable def RunMu_env0 : Prop := Run (eA := e0)
noncomputable def RunMu_diag : Prop := Run (diag := true)
noncomputable def RunMu_noCell : Prop := Run (noCell := true)
noncomputable def RunMu_root : Prop := Run (root := NmHttpX)
noncomputable def RunMu_chkRoot : Prop := Run (chkRoot := NmHttpX)

/-- v5 = v4's expected statement with the three conditions' premises off -/
noncomputable def Fin5_real : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false)
noncomputable def Fin5Mu_v4 : Prop := FD4
noncomputable def Fin5Mu_defsKept : Prop := FD4 (nCtors := false) (nRec := false)
noncomputable def Fin5Mu_ctorsKept : Prop := FD4 (nDefs := false) (nRec := false)
noncomputable def Fin5Mu_recKept : Prop := FD4 (nDefs := false) (nCtors := false)
noncomputable def Fin5Mu_hcd : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (keepHcd := true)
noncomputable def Fin5Mu_carrierZ : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)
noncomputable def Fin5Mu_diag : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (diag := true)
noncomputable def Fin5Mu_concEnd : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (cE := eE)
noncomputable def Fin5Mu_reachEnd : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (eA := eE)
noncomputable def Fin5Mu_root : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (root := NmHttpX)
noncomputable def Fin5Mu_noAdm : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needAdm := false)
noncomputable def Fin5Mu_noKgf : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false)
noncomputable def Fin5Mu_noC1 : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (c1 := false)
noncomputable def Fin5Mu_noC2 : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (c2 := false)

def unfold44 : List Name := [``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT]
def norm44 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold44.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck44 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- 1. soundness of the checker
  let snd ← norm44 (← tyOf ``Tools.ShippingFGCircuitS2zEnvCheck.hftEnvCheckB_sound)
  Tests.Gen5.FGCircuitCmp.checkSame "hftEnvCheckB_sound" snd (← norm37 (Q "Snd_real"))
  for mu in ["SndMu_env1", "SndMu_env2", "SndMu_env3", "SndMu_only1", "SndMu_only2", "SndMu_only3", "SndMu_no1", "SndMu_no2", "SndMu_no3", "SndMu_none",
      "SndMu_dropDef", "SndMu_emptyDef", "SndMu_emptyCtor", "SndMu_false", "SndMu_recOnly", "SndMu_defsOnly"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"hftEnvCheckB_sound vs {mu}" snd (← norm37 (Q mu)); nm := nm + 1
  -- 2. soundness of the entry's check at the pilot root
  let st ← norm44 (← tyOf ``Tools.ShippingFGCircuitS2zPin.startEnvOk_sound)
  Tests.Gen5.FGCircuitCmp.checkSame "startEnvOk_sound" st (← norm37 (Q "Strt_real"))
  for mu in ["StrtMu_root", "StrtMu_env1", "StrtMu_env2", "StrtMu_env3", "StrtMu_only1", "StrtMu_no2", "StrtMu_no3", "StrtMu_dropDef", "StrtMu_false"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"startEnvOk_sound vs {mu}" st (← norm37 (Q mu)); nm := nm + 1
  -- 3. a successful run passed the check at its START environment
  let rn ← norm44 (← tyOf ``Tools.ShippingFGCircuitS2zFinal.startEnvOk_of_run)
  Tests.Gen5.FGCircuitCmp.checkSame "startEnvOk_of_run" rn (← norm37 (Q "Run_real"))
  for mu in ["RunMu_end", "RunMu_env0", "RunMu_diag", "RunMu_noCell", "RunMu_root", "RunMu_chkRoot"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"startEnvOk_of_run vs {mu}" rn (← norm37 (Q mu)); nm := nm + 1
  -- 4. v5
  let f5 ← norm44 (← tyOf ``Tools.ShippingFGCircuitS2zFinal.synth_hftPcieOutByte_finalOffCombined5)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined5" f5 (← norm37 (Q "Fin5_real"))
  for mu in ["Fin5Mu_v4", "Fin5Mu_defsKept", "Fin5Mu_ctorsKept", "Fin5Mu_recKept", "Fin5Mu_hcd", "Fin5Mu_carrierZ", "Fin5Mu_diag", "Fin5Mu_concEnd", "Fin5Mu_reachEnd",
      "Fin5Mu_root", "Fin5Mu_noAdm", "Fin5Mu_noKgf", "Fin5Mu_noC1", "Fin5Mu_noC2"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined5 vs {mu}" f5 (← norm37 (Q mu)); nm := nm + 1
  -- v4 (hypotheses kept) is not v5
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined5 vs the v4 theorem's type" f5 (← Tests.Gen5.FGCircuitPilotCheck43.norm43 (← tyOf ``Tools.ShippingFGCircuitS2yFinal.synth_hftPcieOutByte_finalOffCombined4)); nm := nm + 1
  logInfo m!"FGCIRCUIT44 SIGNATURES: the complete types of hftEnvCheckB_sound, startEnvOk_sound, startEnvOk_of_run and synth_hftPcieOutByte_finalOffCombined5 equal the independently written statements under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths); {nm} mutants rejected"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS2zEnvCheck.hftEnvCheckB_sound, ``Tools.ShippingFGCircuitS2zPin.startEnvOk_sound,
    ``Tools.ShippingFGCircuitS2zFinal.startEnvOk_of_run, ``Tools.ShippingFGCircuitS2zFinal.synth_hftPcieOutByte_finalOffCombined5, ``Tools.ShippingFGCircuitS1qLinked.core_envOkOff]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT44 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck44
