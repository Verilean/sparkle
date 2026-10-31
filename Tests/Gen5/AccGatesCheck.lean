import Tools.ShippingGen5AccGates
import Tests.Gen5.AccCheck
-- Built in the Pod (g5ac-r10) at 5b542e30 (the Check was built on the committed tree): `kjob lake build Tools.ShippingGen5AccGates` (722 jobs) and `kjob lake build Tests.Gen5.AccGatesCheck` (725 jobs), each exit 0. TYPE 2 (definition by body + theorem, both syntactic, no isDefEq fallback) / MUTANT 4 (signature/defeq rejection, not semantic: 3 on GateRunsAt, 1 on gatesNoneAt_of_gateRunsAt) / AXIOMS 2 standard three only / CLOSURE OK 7808 constants (unknown 0) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. Clean issue-linked build ac10v-00f1b849 (exit 0, 725 jobs, src=base=end, dirty=false) approved at 00f1b849. No sorry / axiom / native_decide in this source; the 6 `sorry` warnings of the build are the intended walker-control negatives: 3 at the walkerControls line of Tests/Gen5/AccCheck.lean (:238) and 3 at the walkerControls line of this file (:96).

/-! # DG-ACC unit A6b checks (Tools/ShippingGen5AccGates.lean; scripts/gen5/DG_ACC_FREEZE_REV5.md §2)

TYPE: the definition `GateRunsAt` (the compared statement is the definition BODY) and the theorem `gatesNoneAt_of_gateRunsAt` are each compared
binder by binder (`checkExpected`) with an independently written `Expected…` statement (written from the prose of REV5 §2, not copied from the
implementation file).
MUTANT: one-place, well-typed changes (a dropped conjunct, a dropped `ReadsAt`, a dropped premise), compared with the same reducible comparator as
TYPE and required to be rejected -- a rejection by signature / defeq, NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck` with negative/clean controls and unknown-name controls; roots are put in `seen`. -/
namespace Tests.Gen5.AccGatesCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEntrySoundness (RunsTo)

section Expected

def ExpectedGateRuns (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ wE envR wE' w1 ci w2,
      ReadsAt env₀ cref wE ∧ ReadsAt env₀ cref w1 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none

def ExpectedGatesFromRuns : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop),
    (h : GateRunsAt env₀ mctx mref cctx cref Reach) → GatesNoneAt env₀ Reach

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `GateRunsAt` without the mixed conjunct -/
def MutGRNoMixed (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ wE envR wE' w1 ci w2,
      ReadsAt env₀ cref wE ∧ ReadsAt env₀ cref w1 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none

/-- `GateRunsAt` without `ReadsAt` at `w1` -/
def MutGRNoReadsW1 (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ wE envR wE' w1 ci w2,
      ReadsAt env₀ cref wE ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none

/-- `GateRunsAt` without `ReadsAt` at `wE` -/
def MutGRNoReadsWE (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ wE envR wE' w1 ci w2,
      ReadsAt env₀ cref w1 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none

/-- `gatesNoneAt_of_gateRunsAt` without `h` -/
def MutGatesNoH : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop), GatesNoneAt env₀ Reach

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``GateRunsAt ``ExpectedGateRuns
  checkExpected ``gatesNoneAt_of_gateRunsAt ``ExpectedGatesFromRuns
  checkMutant ``GateRunsAt ``MutGRNoMixed
  checkMutant ``GateRunsAt ``MutGRNoReadsW1
  checkMutant ``GateRunsAt ``MutGRNoReadsWE
  checkMutant ``gatesNoneAt_of_gateRunsAt ``MutGatesNoH

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``GateRunsAt, ``gatesNoneAt_of_gateRunsAt] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path (see AccServedCheck): root / helper value / helper type naming an
absent constant MUST be reported; a clean chain MUST NOT. -/
def unknownControls : MetaM Unit := do
  let ghost := `Ghost.Absent.name
  let addU (n : Name) (type value : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  let unk (roots : List Name) : MetaM (Array Name) := do
    let (_, u, _) ← Tests.Gen5.AccCheck.closureReport (← getEnv) roots
    pure u
  let u1 ← unk [ghost]
  unless u1 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: unknown root not reported ({u1})"
  let u2 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtl.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperVal)
    unk [`Tests.Gen5.UnkCtl.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperTy)
    unk [`Tests.Gen5.UnkCtl.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.CleanHelper)
    unk [`Tests.Gen5.UnkCtl.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``GateRunsAt, ``gatesNoneAt_of_gateRunsAt]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A6b): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccGatesCheck
