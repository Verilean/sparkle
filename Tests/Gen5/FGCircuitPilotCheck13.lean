import Tests.Gen5.FGCircuitPilotCheck10
import Tools.ShippingFGCircuitS1oHead
set_option autoImplicit false
-- FG circuit pilot S1o check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §19.

/-! # FGCircuitPilotCheck13

1. SIGNATURES: complete expected types, written independently of the theorems, for `GetEnvProfileAt.mk`, `headAt_of_profileOff`, `counterLoop_final9P` and the (unapproved, unused) `LogBranchDraft.mk`; one-point MUTANTS rejected: the log branch taken (`o.isSome`), an END / independent world instead of the run's start world, a dropped frame / dropped unset / dropped cell, the old `HeadIO` in place of the run-local premise, another post root, a fused log obligation.
2. HYPS: the explicit hypotheses of `headAt_of_profileOff` and `counterLoop_final9P`; `HeadIO`, `hhead`, `hio` are not among them.
3. NOTUSED / AXIOMS: no theorem of S1oHead (type or value) mentions `HeadIO`, `LogBranchDraft`, `profLogIO`; standard axioms only. -/
namespace Tests.Gen5.FGCircuitPilotCheck13
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1oHead
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEnvSnapshot (EnvFrame)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved coreHead)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises
open Tests.Gen5.FGCircuitPilotCheck5 (W GPd explicitBinders binderInfos)
open Tests.Gen5.FGCircuitPilotCheck7 (ZS ZE)

/-! ## 1. expected statements, written independently -/

/-- `GetEnvProfileAt.mk`. Knobs: the result pinned to `none` (else the log branch `isSome`), the unset premise / the env premise present -/
def ExpMk (pinNone needUnset needEnv : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : W},
    (if needUnset then
      (∀ (o : Option String) (w1 : W), RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref w o w1 →
        (if pinNone then o = none else o.isSome = true))
     else True) →
    (if needEnv then
      (∀ (o : Option String) (w1 : W), RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref w o w1 →
        envAt cref w1 = envAt cref w)
     else True) →
    GetEnvProfileAt mctx mref cctx cref w
def MkTrue := ExpMk true true true
def MutMkLogBranch := ExpMk false true true
def MutMkNoUnset := ExpMk true false true
def MutMkNoEnv := ExpMk true true false
/-- mutant: the lookups are read from an independent world `u`, the structure is stated at `w` -/
def MutMkIndepWorld : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w u : W},
    (∀ (o : Option String) (w1 : W), RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref u o w1 → o = none) →
    (∀ (o : Option String) (w1 : W), RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref u o w1 → envAt cref w1 = envAt cref u) →
    GetEnvProfileAt mctx mref cctx cref w
/-- mutant: the env premise compares the lookup's end world with itself (trivial) -/
def MutMkEndEnv : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : W},
    (∀ (o : Option String) (w1 : W), RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref w o w1 → o = none) →
    (∀ (o : Option String) (w1 : W), RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref w o w1 → envAt cref w1 = envAt cref w1) →
    GetEnvProfileAt mctx mref cctx cref w

/-- `headAt_of_profileOff` (with `HeadAt` unfolded). Knobs: the cell premise, the frame premise -/
def ExpHeadOff (needCell needG : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (X : Lean.Name) {w : W},
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    (if needG then GetEnvProfileAt mctx mref cctx cref w else True) →
    ∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w
def HeadOffTrue := ExpHeadOff true true
def MutHeadOffNoCell := ExpHeadOff false true
def MutHeadOffNoG := ExpHeadOff true false
/-- mutant: the frame premise is at an unrelated world `u` (an end / independent world), the conclusion at `w` -/
def MutHeadOffIndep : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (X : Lean.Name) {w u : W},
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref → GetEnvProfileAt mctx mref cctx cref u →
    ∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w
/-- mutant: the conclusion is for the end world (`envAt w1 = envAt w'`-style: compares with the run's end) -/
def MutHeadOffConclEnd : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (X : Lean.Name) {w : W},
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref → GetEnvProfileAt mctx mref cctx cref w →
    ∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w1
/-- mutant: the old HeadIO premise in place of the run-local frame -/
def MutHeadOffHeadIO : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (X : Lean.Name) {w : W},
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref → HeadIO mctx mref cctx cref →
    ∀ (s : CoreSaved) (w1 : W), RunsTo (coreHead X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w

/-- `counterLoop_final9P`. Knobs: the world of the frame premise (`gw`), the world of the link, the environment of the conclusion, the post root, the cell / frame premise, `useHio` (the old premise instead) -/
def ExpF9P (gw rdw : W → W → W) (eC : Environment → ST.Ref IO.RealWorld Core.State → W → W → Environment) (postRoot : Name)
    (needCell needG useHio : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {ι : Type} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (if needCell then CellPrem Tools.ShippingChildFresh.MkRefd mref cref else True) →
    (if needG then (if useHio then HeadIO mctx mref cctx cref else GetEnvProfileAt mctx mref cctx cref (gw w w')) else True) →
    ReadsAt env₀ cref (rdw w w') →
    entryGatesB env₀ ``counterLoop = true →
    QuoteAt env₀ ``counterLoop counterLoopType counterLoopValue →
    ReaderAt lvl env₀ ``counterLoop counterLoop.machineData →
    (∃ raw, PostRun mctx mref cctx cref w postRoot D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (eC env₀ cref w w') (GPd (ι := ι) lvl (eC env₀ cref w w'))
        (PostRun mctx mref cctx cref w postRoot D') ``counterLoop shCounter mm b D' p
def F9PTrue := ExpF9P (fun w _ => w) (fun w _ => w) ZS ``counterLoop true true false
def M9PGEnd := ExpF9P (fun _ w' => w') (fun w _ => w) ZS ``counterLoop true true false
def M9PLinkEnd := ExpF9P (fun w _ => w) (fun _ w' => w') ZS ``counterLoop true true false
def M9PConclEnd := ExpF9P (fun w _ => w) (fun w _ => w) ZE ``counterLoop true true false
def M9PPost := ExpF9P (fun w _ => w) (fun w _ => w) ZS ``shift4Loop true true false
def M9PNoCell := ExpF9P (fun w _ => w) (fun w _ => w) ZS ``counterLoop false true false
def M9PNoG := ExpF9P (fun w _ => w) (fun w _ => w) ZS ``counterLoop true false false
def M9PHeadIO := ExpF9P (fun w _ => w) (fun w _ => w) ZS ``counterLoop true true true

/-- the (unapproved) log-branch draft, split into the stderr callback and the fixed Handle operations -/
def ExpLogMk (needStderr needHandle fusedStderr : Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State},
    (if needStderr then
      (∀ msg : String, EnvFrame (liftM (do IO.eprintln msg; Sparkle.Compiler.flushStderr : IO Unit) : MetaM Unit) mctx mref cctx cref)
     else True) →
    (if needHandle then
      (∀ msg : String, EnvFrame (liftM (do
        let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
        h.putStrLn msg
        h.flush : IO Unit) : MetaM Unit) mctx mref cctx cref)
     else True) →
    LogBranchDraft mctx mref cctx cref
def LogMkTrue := ExpLogMk true true false
def MutLogNoStderr := ExpLogMk false true false
def MutLogNoHandle := ExpLogMk true false false
/-- mutant: the stderr part drops the flush -/
def MutLogEprintOnly : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State},
    (∀ msg : String, EnvFrame (liftM (IO.eprintln msg : IO Unit) : MetaM Unit) mctx mref cctx cref) →
    (∀ msg : String, EnvFrame (liftM (do
        let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
        h.putStrLn msg
        h.flush : IO Unit) : MetaM Unit) mctx mref cctx cref) →
    LogBranchDraft mctx mref cctx cref
/-- mutant: the handle part writes another path -/
def MutLogPath : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State},
    (∀ msg : String, EnvFrame (liftM (do IO.eprintln msg; Sparkle.Compiler.flushStderr : IO Unit) : MetaM Unit) mctx mref cctx cref) →
    (∀ msg : String, EnvFrame (liftM (do
        let h ← IO.FS.Handle.mk "/tmp/other.log" .append
        h.putStrLn msg
        h.flush : IO Unit) : MetaM Unit) mctx mref cctx cref) →
    LogBranchDraft mctx mref cctx cref

def whitelist : List Name := [``ExpMk, ``MkTrue, ``MutMkLogBranch, ``MutMkNoUnset, ``MutMkNoEnv, ``MutMkIndepWorld, ``MutMkEndEnv,
  ``ExpHeadOff, ``HeadOffTrue, ``MutHeadOffNoCell, ``MutHeadOffNoG, ``MutHeadOffIndep, ``MutHeadOffConclEnd, ``MutHeadOffHeadIO,
  ``ExpF9P, ``F9PTrue, ``M9PGEnd, ``M9PLinkEnd, ``M9PConclEnd, ``M9PPost, ``M9PNoCell, ``M9PNoG, ``M9PHeadIO,
  ``ExpLogMk, ``LogMkTrue, ``MutLogNoStderr, ``MutLogNoHandle, ``MutLogEprintOnly, ``MutLogPath,
  ``Tests.Gen5.FGCircuitPilotCheck7.ZS, ``Tests.Gen5.FGCircuitPilotCheck7.ZE, ``Tests.Gen5.FGCircuitPilotCheck5.GPd,
  -- definitions under test
  ``HeadAt, ``profileAct]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withDefault (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
    let ba ← binderInfos a
    let be ← binderInfos e
    unless ba == be do throwError "{thm}: binder kinds differ from {exp}: {repr ba} vs {repr be}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withDefault (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S := `Tools.ShippingFGCircuitS1oHead
  let mut nm : Nat := 0
  same (S ++ `GetEnvProfileAt.mk) ``MkTrue
  for mu in [``MutMkLogBranch, ``MutMkNoUnset, ``MutMkNoEnv, ``MutMkIndepWorld, ``MutMkEndEnv] do differs (S ++ `GetEnvProfileAt.mk) mu; nm := nm + 1
  same (S ++ `headAt_of_profileOff) ``HeadOffTrue
  for mu in [``MutHeadOffNoCell, ``MutHeadOffNoG, ``MutHeadOffIndep, ``MutHeadOffConclEnd, ``MutHeadOffHeadIO] do differs (S ++ `headAt_of_profileOff) mu; nm := nm + 1
  same (S ++ `counterLoop_final9P) ``F9PTrue
  for mu in [``M9PGEnd, ``M9PLinkEnd, ``M9PConclEnd, ``M9PPost, ``M9PNoCell, ``M9PNoG, ``M9PHeadIO] do differs (S ++ `counterLoop_final9P) mu; nm := nm + 1
  same (S ++ `LogBranchDraft.mk) ``LogMkTrue
  for mu in [``MutLogNoStderr, ``MutLogNoHandle, ``MutLogEprintOnly, ``MutLogPath] do differs (S ++ `LogBranchDraft.mk) mu; nm := nm + 1
  logInfo m!"FGCIRCUIT13 SIGNATURES: GetEnvProfileAt.mk, headAt_of_profileOff, counterLoop_final9P, LogBranchDraft.mk (draft): complete types match the independently written statements; {nm} mutants rejected (the log branch taken (isSome), the lookup read at an independent world, a trivial end-world env premise, dropped unset / env / cell / frame premise, the frame at an unrelated world, the conclusion at the end world, the old HeadIO in place of the run-local frame, link / frame / conclusion at the END world, another post root, a draft without the stderr / handle part, without the flush, with another path)"

/-! ## 2. the hypotheses that remain -/

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1oHead
  let bs ← explicitBinders (S ++ `counterLoop_final9P)
  let names := (bs.map (·.1)).filter fun n => !n.startsWith "a._@"
  let expected := ["L", "lvl", "env₀", "hstart", "hr", "hcell", "hg", "hread", "hgatesB", "hquote", "hreader"]
  unless names == expected do throwError "counterLoop_final9P: hypotheses are {names}, expected {expected}"
  for gone in ["hio", "hhead", "hquiet", "hdRun", "hsrc", "hchk"] do
    if names.contains gone then throwError "counterLoop_final9P: {gone} is a hypothesis"
  for (n, t) in bs do
    let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<unprintable; constants: {t.getUsedConstants.toList.map (·.toString)}>"
    logInfo m!"FGCIRCUIT13 REMAINING counterLoop_final9P {n} : {pp}"
  let bs2 ← explicitBinders (S ++ `headAt_of_profileOff)
  let n2 := (bs2.map (·.1)).filter fun n => !n.startsWith "a._@"
  unless n2 == ["X", "hcell", "hg"] do throwError "headAt_of_profileOff: hypotheses are {n2}"
  logInfo "FGCIRCUIT13 HYPS: headAt_of_profileOff = X hcell(CellPrem MkRefd mref cref) hg(GetEnvProfileAt: at the run's start world w, a run of IO.getEnv \"SPARKLE_PROFILE\" returns none and keeps envAt cref). counterLoop_final9P = L lvl env₀ hstart hr hcell hg hread hgatesB hquote hreader. NOT hypotheses: HeadIO, hhead, hio, hquiet, GetEnvFrame, hdRun, hsrc. hg is a NAMED HYPOTHESIS about the run, not obtained from a Meta observation of the process environment."

/-! ## 3. NOTUSED and axioms -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1oHead
  let names : List Name := [S ++ `headAt_of_profileOff, S ++ `counterLoop_final9P]
  let banned : List Name := [``HeadIO, S ++ `LogBranchDraft, S ++ `logStderrAct, S ++ `logTailAct, ``profLogIO, ``HeadIO.log, ``HeadIO.getEnv, ``envFrame_coreHead, ``headAt_of_cellPrem]
  for nm in names do
    let ci ← getConstInfo nm
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    for b in banned do
      if used.contains b then throwError "{nm} mentions {b}"
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT13 NOTUSED: headAt_of_profileOff and counterLoop_final9P mention none of HeadIO / LogBranchDraft / profLogIO / envFrame_coreHead / headAt_of_cellPrem (direct constants of type and value)"
  logInfo m!"FGCIRCUIT13 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck13
