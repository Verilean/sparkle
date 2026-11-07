import Tools.ShippingFGCircuitS3aFinal
import Tests.Gen5.FGCircuitPilotCheck44
set_option autoImplicit false
-- FG circuit pilot Check45 (S3a2): A) controls of the callee-facts check on the real environment (+ one measurement of the root's Off entry with the extended guard); B) complete types (soundness, run-level fact, v6) against independently written statements, one criterion FGCircuitCmp.stmtEq. docs/FG-CIRCUIT-PILOT.md §50.
open Lean Elab Command Sparkle.Compiler.EnvTableCheck Sparkle.Compiler.KidFactsCheck Sparkle.Compiler.PilotKidTables Tools.ShippingFGCircuitS2gGates
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

run_cmd do
  let env ← getEnv
  let ok (b : Bool) (msg : String) : CommandElabM Unit := unless b do throwError "FGCIRCUIT45 control failed: {msg}"
  let inl := Sparkle.Compiler.Elab.userInliner env
  let ip := Sparkle.Compiler.Elab.instancePredicate env
  let pe := Sparkle.Compiler.Elab.gatePeeledBody
  -- positive: the real environment passes, per callee and for the entry's function
  ok (kidRowOkB env inl ip pe hftHttpName httpT httpV httpVi) "http row true"
  ok (kidRowOkB env inl ip pe hftTlpName tlpT tlpV tlpVi) "tlp row true"
  ok (kidsOkB env inl ip pe) "kidsOkB true on the real environment"
  ok (startKidsOk Tools.ShippingFGCircuitS1kStmt.hftRoot env inl ip pe) "startKidsOk true at the root"
  ok (startKidsOk `Some.Other.Decl env (fun e => e) (fun _ => true) pe) "other declarations unconstrained (documented: no guarantee for them)"
  -- the generated terms are the real ones (also pinned in the kernel by S3aKids)
  ok (exprEqB httpT httpType && exprEqB httpV httpValue && exprEqB httpVi httpInlValue && exprEqB tlpT tlpType && exprEqB tlpV tlpValue && exprEqB tlpVi tlpInlValue) "generated terms equal the quotes"
  -- negative: each fact altered
  let z := mkNatLit 0
  ok (!kidRowOkB env inl ip pe hftHttpName z httpV httpVi) "type altered"
  ok (!kidRowOkB env inl ip pe hftHttpName httpT z httpVi) "value altered"
  ok (!kidRowOkB env inl ip pe hftHttpName httpT httpV z) "inlined value altered"
  ok (!kidRowOkB env inl ip pe hftTlpName httpT httpV httpVi) "another callee's terms (tlp name, http terms)"
  ok (!kidRowOkB env inl ip pe hftHttpName tlpT tlpV tlpVi) "another callee's terms (http name, tlp terms)"
  ok (!kidRowOkB env inl ip pe `Sparkle.NoSuchConstant httpT httpV httpVi) "missing constant"
  ok (!kidRowOkB env (fun e => e) ip pe hftHttpName httpT httpV httpVi) "inliner that does nothing (V is not sent to Vi)"
  ok (!kidRowOkB env (fun e => if exprEqB e httpT then z else inl e) ip pe hftHttpName httpT httpV httpVi) "inliner that does not fix the type"
  ok (!kidRowOkB env inl (fun _ => true) pe hftHttpName httpT httpV httpVi) "instance predicate true everywhere"
  ok (!kidRowOkB env inl (fun e => exprEqB e (pe httpV) || ip e) pe hftHttpName httpT httpV httpVi) "instance predicate true at the peeled value"
  ok (!kidRowOkB env inl (fun e => exprEqB e (pe httpVi) || ip e) pe hftHttpName httpT httpV httpVi) "instance predicate true at the peeled inlined value"
  ok (!kidsOkB env inl (fun e => exprEqB e (pe tlpVi) || ip e) pe) "second callee's point true"
  ok (!kidsOkB env inl (fun _ => true) pe) "kidsOkB with ip true"
  ok (!startKidsOk Tools.ShippingFGCircuitS1kStmt.hftRoot env (fun e => e) ip pe) "startKidsOk at the root with a different inliner"
  -- negative: another environment (only `Init` imported)
  let env' ← importModules #[{ module := `Init }] {} (loadExts := false)
  ok (!kidsOkB env' inl ip pe) "check false on the Init-only environment"
  logInfo "FGCIRCUIT45 CONTROLS: ok (real env true; type/value/inlined value/swapped callee/missing/inliner/type-fixing/ip everywhere/ip at either point/second callee/Init-only false)"

-- one measurement (not a cost claim): the root's Off entry (both checks) against the unchanged `synthesizeCombinational`
run_cmd liftTermElabM do
  let X := Tools.ShippingFGCircuitS1kStmt.hftRoot
  let t0 ← IO.monoMsNow
  let (m1, d1) ← Sparkle.Compiler.Elab.synthesizeCombinationalOff X
  let t1 ← IO.monoMsNow
  let (m2, d2) ← Sparkle.Compiler.Elab.synthesizeCombinational X
  let t2 ← IO.monoMsNow
  let env ← getEnv
  unless startKidsOk X env (Sparkle.Compiler.Elab.userInliner env) (Sparkle.Compiler.Elab.instancePredicate env) Sparkle.Compiler.Elab.gatePeeledBody && Sparkle.Compiler.PilotEnvTables.startEnvOk X env do
    throwError "FGCIRCUIT45: the checks are false on the real environment"
  let a := toString (repr m1) ++ "\n" ++ toString (repr d1)
  let b := toString (repr m2) ++ "\n" ++ toString (repr d2)
  unless a == b do throwError "FGCIRCUIT45 REPR: the Off entry (with checks) and the unchanged entry differ"
  logInfo m!"FGCIRCUIT45 REPR: module+design repr identical ({(toString (repr m1)).length} / {(toString (repr d1)).length} chars); Off with both checks {t1-t0} ms, unchanged entry {t2-t1} ms (ONE run each; the checks alone are not timed separately; not a cost claim)"

/-! ## B. complete types against independently written statements (ONE criterion `FGCircuitCmp.stmtEq` for the expected statement and every mutant) -/
namespace Tests.Gen5.FGCircuitPilotCheck45
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kStmt (hftRoot hftHttp hftTlp)
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 EntryOf)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)
open Tests.Gen5.FGCircuitPilotCheck43 (FD4)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck27 (ExpHK MuSwap MuSwapName MuHttpTwice MuTlpTwice MuHttpOnly MuTlpOnly MuWholeBoth MuTrue)
open Tests.Gen5.FGCircuitPilotCheck44 (envX NmHttpX)
open Sparkle.Compiler.Elab (userInliner instancePredicate gatePeeledBody)
open Sparkle.Compiler.PilotKidTables (startKidsOk)

def idPeel (e : Lean.Expr) : Lean.Expr := e

/-- the soundness statement of the callee check, written again. Knobs: the declaration the check is asked for, its result, the environment the check is run at and the one the conclusion speaks about, the inliner / instance predicate / peel, the conclusion -/
noncomputable def ExpKSnd (X : Name) (val : Bool) (ec : Environment → Environment) (inl : Environment → Lean.Expr → Lean.Expr) (ip : Environment → Lean.Expr → Bool)
    (peel : Lean.Expr → Lean.Expr) (C : Environment → Prop) (ee : Environment → Environment) : Prop :=
  ∀ {env : Environment}, startKidsOk X (ec env) (inl (ec env)) (ip (ec env)) peel = val → C (ee env)

noncomputable def KSnd (X : Name := hftRoot) (val : Bool := true) (ec : Environment → Environment := fun e => e)
    (inl : Environment → Lean.Expr → Lean.Expr := userInliner) (ip : Environment → Lean.Expr → Bool := instancePredicate)
    (peel : Lean.Expr → Lean.Expr := gatePeeledBody) (C : Environment → Prop := ExpHK) (ee : Environment → Environment := fun e => e) : Prop :=
  ExpKSnd X val ec inl ip peel C ee

/-- the run-level fact, written again: a run of the entry on `root` from `w` to `w'`, with the cell premise, passed the callee check at `eA`, with the inliner / instance predicate of the environment `eI` -/
noncomputable def ExpRunK (diag needCell : Bool) (root chkRoot : Name) (eA eI : EnvK) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tests.Gen5.FGCircuitPilotCheck26.Pre needCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w' →
    startKidsOk chkRoot (eA cref w w' (envX (envAt cref w))) (userInliner (eI cref w w' (envX (envAt cref w)))) (instancePredicate (eI cref w w' (envX (envAt cref w)))) gatePeeledBody = true)

noncomputable def RunK (diag : Bool := false) (needCell : Bool := true) (root : Name := hftRoot) (chkRoot : Name := hftRoot) (eA : EnvK := eS) (eI : EnvK := eS) : Prop :=
  ExpRunK diag needCell root chkRoot eA eI

/-! mutants -/
noncomputable def KSnd_real : Prop := KSnd
noncomputable def KSndMu_root : Prop := KSnd (X := NmHttpX)
noncomputable def KSndMu_false : Prop := KSnd (val := false)
noncomputable def KSndMu_concl : Prop := KSnd (ee := envX)
noncomputable def KSndMu_inl : Prop := KSnd (inl := fun _ => idPeel)
noncomputable def KSndMu_ip : Prop := KSnd (ip := fun _ _ => false)
noncomputable def KSndMu_peel : Prop := KSnd (peel := idPeel)
noncomputable def KSndMu_swap : Prop := KSnd (C := MuSwap)
noncomputable def KSndMu_swapName : Prop := KSnd (C := MuSwapName)
noncomputable def KSndMu_httpTwice : Prop := KSnd (C := MuHttpTwice)
noncomputable def KSndMu_tlpTwice : Prop := KSnd (C := MuTlpTwice)
noncomputable def KSndMu_httpOnly : Prop := KSnd (C := MuHttpOnly)
noncomputable def KSndMu_tlpOnly : Prop := KSnd (C := MuTlpOnly)
noncomputable def KSndMu_whole : Prop := KSnd (C := MuWholeBoth)
noncomputable def KSndMu_true : Prop := KSnd (C := MuTrue)
noncomputable def KSndMu_ecEnv : Prop := KSnd (ec := envX)

noncomputable def RunK_real : Prop := RunK
noncomputable def RunKMu_end : Prop := RunK (eA := eE)
noncomputable def RunKMu_env0 : Prop := RunK (eA := e0)
noncomputable def RunKMu_inlEnd : Prop := RunK (eI := eE)
noncomputable def RunKMu_inlEnv0 : Prop := RunK (eI := e0)
noncomputable def RunKMu_diag : Prop := RunK (diag := true)
noncomputable def RunKMu_noCell : Prop := RunK (needCell := false)
noncomputable def RunKMu_root : Prop := RunK (root := NmHttpX)
noncomputable def RunKMu_chkRoot : Prop := RunK (chkRoot := NmHttpX)

/-- v6 = v4's expected statement with the premises of the three environment conditions and of `hkgfacts` off -/
noncomputable def Fin6_real : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false)
noncomputable def Fin6Mu_v5 : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false)
noncomputable def Fin6Mu_v4 : Prop := FD4
noncomputable def Fin6Mu_defsKept : Prop := FD4 (nCtors := false) (nRec := false) (needKgf := false)
noncomputable def Fin6Mu_ctorsKept : Prop := FD4 (nDefs := false) (nRec := false) (needKgf := false)
noncomputable def Fin6Mu_recKept : Prop := FD4 (nDefs := false) (nCtors := false) (needKgf := false)
noncomputable def Fin6Mu_hcd : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (keepHcd := true)
noncomputable def Fin6Mu_carrierZ : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (CV := Tools.ShippingFGCircuitS1tFinal.cdvZ)
noncomputable def Fin6Mu_diag : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (diag := true)
noncomputable def Fin6Mu_concEnd : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (cE := eE)
noncomputable def Fin6Mu_reachEnd : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (eA := eE)
noncomputable def Fin6Mu_root : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (root := NmHttpX)
noncomputable def Fin6Mu_noAdm : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (needAdm := false)
noncomputable def Fin6Mu_noC1 : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (c1 := false)
noncomputable def Fin6Mu_noC2 : Prop := FD4 (nDefs := false) (nCtors := false) (nRec := false) (needKgf := false) (c2 := false)

def unfold45 : List Name := [``Tools.ShippingFGCircuitS3aFinal.HftFinalStmtOffCombined6, ``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT]
def norm45 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold45.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck45 ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- 1. soundness of the entry's callee check at the pilot root
  let snd ← norm45 (← tyOf ``Tools.ShippingFGCircuitS3aKids.startKidsOk_sound)
  Tests.Gen5.FGCircuitCmp.checkSame "startKidsOk_sound" snd (← norm37 (Q "KSnd_real"))
  for mu in ["KSndMu_root", "KSndMu_false", "KSndMu_concl", "KSndMu_inl", "KSndMu_ip", "KSndMu_peel", "KSndMu_swap", "KSndMu_swapName", "KSndMu_httpTwice",
      "KSndMu_tlpTwice", "KSndMu_httpOnly", "KSndMu_tlpOnly", "KSndMu_whole", "KSndMu_true", "KSndMu_ecEnv"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"startKidsOk_sound vs {mu}" snd (← norm37 (Q mu)); nm := nm + 1
  -- 2. a successful run passed the check at its START environment, with the compiler's own functions at that environment
  let rn ← norm45 (← tyOf ``Tools.ShippingFGCircuitS3aFinal.startKidsOk_of_run)
  Tests.Gen5.FGCircuitCmp.checkSame "startKidsOk_of_run" rn (← norm37 (Q "RunK_real"))
  for mu in ["RunKMu_end", "RunKMu_env0", "RunKMu_inlEnd", "RunKMu_inlEnv0", "RunKMu_diag", "RunKMu_noCell", "RunKMu_root", "RunKMu_chkRoot"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"startKidsOk_of_run vs {mu}" rn (← norm37 (Q mu)); nm := nm + 1
  -- 3. v6
  let f6 ← norm45 (← tyOf ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined6" f6 (← norm37 (Q "Fin6_real"))
  for mu in ["Fin6Mu_v5", "Fin6Mu_v4", "Fin6Mu_defsKept", "Fin6Mu_ctorsKept", "Fin6Mu_recKept", "Fin6Mu_hcd", "Fin6Mu_carrierZ", "Fin6Mu_diag", "Fin6Mu_concEnd", "Fin6Mu_reachEnd",
      "Fin6Mu_root", "Fin6Mu_noAdm", "Fin6Mu_noC1", "Fin6Mu_noC2"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined6 vs {mu}" f6 (← norm37 (Q mu)); nm := nm + 1
  -- the v5 theorem's type (hkgfacts kept) is not v6
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined6 vs the v5 theorem's type" f6 (← norm45 (← tyOf ``Tools.ShippingFGCircuitS2zFinal.synth_hftPcieOutByte_finalOffCombined5)); nm := nm + 1
  logInfo m!"FGCIRCUIT45 SIGNATURES: the complete types of startKidsOk_sound, startKidsOk_of_run and synth_hftPcieOutByte_finalOffCombined6 equal the independently written statements under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths); {nm} mutants rejected (other root, result false, conclusion at another environment, identity inliner / false instance predicate / unpeeled body, swapped / repeated / single / whole-value callee facts, True, check at another environment, start/end/env₀ worlds, inliner at another world, diagnostic entry, cell premise dropped, kept hypotheses, carrier, premises dropped, v5 and v4)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3aKids.startKidsOk_sound, ``Tools.ShippingFGCircuitS3aFinal.startKidsOk_of_run,
    ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6, ``Tools.ShippingFGCircuitS1qLinked.core_kidsOkOff,
    ``Sparkle.Compiler.KidFactsCheck.kidRowOkB_sound]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT45 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck45
