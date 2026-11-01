import Tools.ShippingGen5AccReader
import Tests.Gen5.AccCheck
-- Clean issue-linked build `acv-d9a894b2` exit 0, 737 jobs (approved at d9a894b2). Pod build (g5ac-r12) at 46600383 (Check built on the committed tree), exit 0, 737 jobs. TYPE 4 (2 definitions by body + 2 theorems) / MUTANT 5 (signature/defeq rejection, not semantic: 1 ReaderGateShape, 1 ReaderRunsAt, 2 gateRunsAt_of_readerRuns, 1 gatesNoneAt_of_readerRuns) / AXIOMS 2 standard three only / CLOSURE OK 8038 constants (unknown 0) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. The 3 sorry warnings are the intended walker-control negatives (Tests/Gen5/AccReaderCheck.lean:107); AccCheck's own 3 are the same kind.

/-! # DG-ACC unit A6c checks (Tools/ShippingGen5AccReader.lean; scripts/gen5/DG_ACC_FREEZE_REV6.md §2)

TYPE: the 2 definitions (compared by BODY) and the 2 theorems are each compared binder by binder (`checkExpected`) with an independently written
`Expected…` statement (written from the prose of REV6 §1, not copied from the implementation file).
MUTANT: one-place, well-typed changes, compared with the same reducible comparator as TYPE and required to be rejected -- a rejection by
signature / defeq, NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck`, unknown controls, roots in `seen`. -/
namespace Tests.Gen5.AccReaderCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineCommand (Read readMachine)
open Tools.ShippingEnvSnapshot (GetEnvFrame)

section Expected

-- for one name: any successful reader run yields the linked getEnv / getConstInfo runs and both gate refusals on the written-out entry
def ExpectedShape (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) : Prop :=
  ∀ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
    RunsTo (readMachine c false) mctx mref cctx cref w r w' →
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
        (instancePredicate env) = none

def ExpectedReaderRuns (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
      ReadsAt env₀ cref w ∧ RunsTo (readMachine c false) mctx mref cctx cref w r w'

def ExpectedGateFromReader : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop),
    (hg : GetEnvFrame mctx mref cctx cref) → (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c) →
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) → GateRunsAt env₀ mctx mref cctx cref Reach

def ExpectedNoneFromReader : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop),
    (hg : GetEnvFrame mctx mref cctx cref) → (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c) →
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) → GatesNoneAt env₀ Reach

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `ReaderGateShape` without the mixed conjunct -/
def MutShapeNoMixed (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) : Prop :=
  ∀ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
    RunsTo (readMachine c false) mctx mref cctx cref w r w' →
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) = none

/-- `ReaderRunsAt` without `ReadsAt` -/
def MutRunsNoReads (env₀ : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ ci₀, env₀.find? c = some ci₀ →
    ∃ (w : Void IO.RealWorld) (r : Read) (w' : Void IO.RealWorld),
      RunsTo (readMachine c false) mctx mref cctx cref w r w'

/-- `gateRunsAt_of_readerRuns` without `hg` -/
def MutGateNoHg : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop),
    (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c) →
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) → GateRunsAt env₀ mctx mref cctx cref Reach

/-- `gateRunsAt_of_readerRuns` without `hshape` -/
def MutGateNoShape : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop),
    (hg : GetEnvFrame mctx mref cctx cref) →
    (h : ReaderRunsAt env₀ mctx mref cctx cref Reach) → GateRunsAt env₀ mctx mref cctx cref Reach

/-- `gatesNoneAt_of_readerRuns` without `h` -/
def MutNoneNoH : Prop :=
  ∀ {env₀ : Environment} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (Reach : Name → Prop),
    (hg : GetEnvFrame mctx mref cctx cref) → (hshape : ∀ c, Reach c → ReaderGateShape mctx mref cctx cref c) →
    GatesNoneAt env₀ Reach

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``ReaderGateShape ``ExpectedShape
  checkExpected ``ReaderRunsAt ``ExpectedReaderRuns
  checkExpected ``gateRunsAt_of_readerRuns ``ExpectedGateFromReader
  checkExpected ``gatesNoneAt_of_readerRuns ``ExpectedNoneFromReader
  checkMutant ``ReaderGateShape ``MutShapeNoMixed
  checkMutant ``ReaderRunsAt ``MutRunsNoReads
  checkMutant ``gateRunsAt_of_readerRuns ``MutGateNoHg
  checkMutant ``gateRunsAt_of_readerRuns ``MutGateNoShape
  checkMutant ``gatesNoneAt_of_readerRuns ``MutNoneNoH

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``gateRunsAt_of_readerRuns, ``gatesNoneAt_of_readerRuns] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path: root / helper value / helper type naming an absent constant MUST be
reported; a clean chain MUST NOT. -/
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
  let roots := [``ReaderGateShape, ``ReaderRunsAt, ``gateRunsAt_of_readerRuns, ``gatesNoneAt_of_readerRuns]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A6c): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccReaderCheck
