import Tools.ShippingGen5EnvR
import Tests.Gen5.EnvCheck
set_option autoImplicit false
-- Built in g5envr-8ebda2f3 (clean, exit 0, 749 jobs): TYPE 3, MUTANT 3 signature/defeq rejections, controls 2 (each also
-- hits its intended constant alone), REACH 2, AXIOMS 2. No sorry / axiom / native_decide.

/-! # DG-ENV unit (a) checks (Tools/ShippingGen5EnvR.lean; scripts/gen5/DG_ENV_FREEZE.md rev2.1 §4.4.3)

1. TYPE: `MachineDefinesR`'s body against an independent `ExpMachineDefinesR`; R1, R2 against the freeze statements.
2. MUTANT (signature/defeq rejections, NOT semantic counterexamples): `MachineDefinesR` without the `w7` premise;
   R2 without `hc`; R1 in the converse direction (`MachineDefinesR ⇒ MachineDefines`).
3. CLOSURE: the detector of Tests/Gen5/EnvCheck.lean (`reach`, `forbidConsts`; its 10 controls run there), re-run on
   two of its controls here, then on R1/R2.
4. Axioms. -/

namespace Tests.Gen5.EnvRCheck
open Lean Meta
open Sparkle.Compiler.Elab (instancePredicate userInliner structEnv entryConst certifiedShape? mixedCertifiedShape?
  machineShape? MachineShape)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5Env
open Tests.Gen3.ExpectedType

def ExpMachineDefinesR (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ w1 ci w2 w5 envR w6 w7 envR' w8,
    ReadsAt env₀ cref w1 → ReadsAt env₀ cref w5 → ReadsAt env₀ cref w7 →
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (structEnv envR') = some shape

def MutMachineDefinesRNoW7 (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ w1 ci w2 w5 envR w6 w7 envR' w8,
    ReadsAt env₀ cref w1 → ReadsAt env₀ cref w5 →
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (instancePredicate envR) = none ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) (structEnv envR') = some shape

def ExpR1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {declName : Name} {shape : MachineShape}
    (h : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName shape),
    MachineDefinesR env₀ mctx mref cctx cref declName shape

def MutR1Conv : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {declName : Name} {shape : MachineShape}
    (h : MachineDefinesR env₀ mctx mref cctx cref declName shape),
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName shape

def ExpR2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {c : Name} {ci₀ : ConstantInfo} {shape : MachineShape}
    (hc : env₀.find? c = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape),
    MachineDefinesR env₀ mctx mref cctx cref c shape

def MutR2NoHc : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {c : Name} {ci₀ : ConstantInfo} {shape : MachineShape}
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape),
    MachineDefinesR env₀ mctx mref cctx cref c shape

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``MachineDefinesR ``ExpMachineDefinesR
  checkExpected ``machineDefinesR_of_defines ``ExpR1
  checkExpected ``machineDefinesR_of_env ``ExpR2
  checkMutant ``MachineDefinesR ``MutMachineDefinesRNoW7
  checkMutant ``machineDefinesR_of_defines ``MutR1Conv
  checkMutant ``machineDefinesR_of_env ``MutR2NoHc

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← Tests.Gen5.EnvCheck.forbidConsts
  let F := `Tests.Gen5.EnvFixture
  for (c, t) in [(F ++ `badND, ``Tools.ShippingGen2.T1HypND.defines),
      (F ++ `badGetEnvFrame, ``Tools.ShippingEnvSnapshot.GetEnvFrame)] do
    let r ← Tests.Gen5.EnvCheck.reach forbid c
    if r.hit.isNone then throwError "ENVR AUDIT FAILED: detector misses {c}"
    let rt ← Tests.Gen5.EnvCheck.reach [t] c
    unless rt.hit.map (·.getLast? == some t) == some true do
      throwError "ENVR AUDIT FAILED: {c} does not reach its intended {t}"
    logInfo m!"ENVR CONTROL {c}: full set {toString r.hit}; intended {t} alone {toString rt.hit}"
  for (c, req) in [(``machineDefinesR_of_defines, [``MachineDefinesR, ``Tools.ShippingMachineEntry.MachineDefines]),
      (``machineDefinesR_of_env, [``MachineDefinesR, ``ci_of_readsAt, ``envR_of_readsAt])] do
    let r ← Tests.Gen5.EnvCheck.reach forbid c
    if let some p := r.hit then throwError "ENVR AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "ENVR AUDIT FAILED {c}: {t} not reached"
    logInfo m!"ENVR REACH {c}: no Laws/RefLawsAOps/RefLawsATele/T1Hyp/T1HypND field (named, raw proj, recursor), no GetEnvFrame/ReadKeeps/EnvSnapshot; reaches {req} (visited {r.visited})"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``machineDefinesR_of_defines, ``machineDefinesR_of_env] do
    checkAxioms n

end Tests.Gen5.EnvRCheck
