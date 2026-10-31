import Tools.ShippingGen5AccCloses
import Tests.Gen5.AccCheck
-- Clean issue-linked build `ac14v-c12df3ef` exit 0, 725 jobs (approved at c12df3ef): TYPE 3 / MUTANT 7 / AXIOMS 1 / CLOSURE 15025 constants, 4 expected suppliers reached; its 6 sorry warnings are the walker-control negatives at AccCheck:238 and AccClosesCheck:110 (3 each). Pod build (g5ac-r14) at 18f10401 (Check built on the committed tree), exit 0, 725 jobs. TYPE 3 (2 definitions by body + 1 theorem) / MUTANT 7 (signature/defeq rejection, not semantic: 2 ClosesData, 1 ClosesCalls, 4 closesOfShape_of_data) / AXIOMS 1 standard three only / CLOSURE OK 15025 constants (unknown 0, 4 expected suppliers reached, DataOf/SemGen units not reached) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. The 3 sorry warnings are the intended walker-control negatives (Tests/Gen5/AccClosesCheck.lean:110).

/-! # DG-ACC unit A7 checks (Tools/ShippingGen5AccCloses.lean; scripts/gen5/DG_ACC_FREEZE_REV7.md §2)

TYPE: the 2 definitions (compared by BODY) and the theorem, each compared binder by binder (`checkExpected`) with an independently written
`Expected…` statement (written from the prose of REV7 §1: three data facts / `CallsClose` for non-empty `insts`, not copied from the implementation).
MUTANT: one-place, well-typed changes compared with the same reducible comparator and required to be rejected -- a rejection by signature / defeq,
NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: explicit-value walker of `AccCheck`; forbidden set `sorryAx / ofReduceBool / trustCompiler`; expected suppliers
must be reached; the A7-excluded supplier units (`ShippingGen5DataOf*`, `ShippingGen5SemGen*`) must not be. -/
namespace Tests.Gen5.AccClosesCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingEntrySoundness Tools.ShippingMachineAuto
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingClosesSplit (CallsClose)
open Tools.ShippingMixedSourceBridge (inputExpr)

section Expected

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

-- for every reached name whose reader data is `d`: d passes ok, d's body is the quotation of the packed term, d passes letsAliasOk
def ExpectedData (K : AssignKit ι dom env₀) (Reach : Name → Prop) : Prop :=
  ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d →
    d.ok = true ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧ d.letsAliasOk = true

-- for every reached name with non-empty insts: CallsClose at every admissible context
def ExpectedCalls (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d → d.shape.insts ≠ [] →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      CallsClose mctx mref cctx cref c d.shape

def ExpectedCloses : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hDS : DataOfShape K) → (hD : ClosesData K Reach) → (hC : ClosesCalls K L Reach) →
    ClosesOfShape env₀ L Reach

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `ClosesData` without `letsAliasOk` -/
def MutDataNoAlias (K : AssignKit ι dom env₀) (Reach : Name → Prop) : Prop :=
  ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d →
    (d.ok = true ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed))

/-- `ClosesData` without the body equation -/
def MutDataNoBody (K : AssignKit ι dom env₀) (Reach : Name → Prop) : Prop :=
  ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d → d.ok = true ∧ d.letsAliasOk = true

/-- `ClosesCalls` without `insts ≠ []` -/
def MutCallsAll (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      CallsClose mctx mref cctx cref c d.shape

/-- `closesOfShape_of_data` without `hDS` -/
def MutNoDS : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hD : ClosesData K Reach) → (hC : ClosesCalls K L Reach) → ClosesOfShape env₀ L Reach

/-- `closesOfShape_of_data` without `hcov` -/
def MutNoCov : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hDS : DataOfShape K) → (hD : ClosesData K Reach) → (hC : ClosesCalls K L Reach) → ClosesOfShape env₀ L Reach

/-- `closesOfShape_of_data` without `hC` -/
def MutNoC : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hDS : DataOfShape K) → (hD : ClosesData K Reach) → ClosesOfShape env₀ L Reach

/-- `closesOfShape_of_data` without `hD` -/
def MutNoD : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hDS : DataOfShape K) → (hC : ClosesCalls K L Reach) → ClosesOfShape env₀ L Reach

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``ClosesData ``ExpectedData
  checkExpected ``ClosesCalls ``ExpectedCalls
  checkExpected ``closesOfShape_of_data ``ExpectedCloses
  checkMutant ``ClosesData ``MutDataNoAlias
  checkMutant ``ClosesData ``MutDataNoBody
  checkMutant ``ClosesCalls ``MutCallsAll
  checkMutant ``closesOfShape_of_data ``MutNoDS
  checkMutant ``closesOfShape_of_data ``MutNoCov
  checkMutant ``closesOfShape_of_data ``MutNoC
  checkMutant ``closesOfShape_of_data ``MutNoD

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``closesOfShape_of_data

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
  let roots := [``ClosesData, ``ClosesCalls, ``closesOfShape_of_data]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  -- expected suppliers that the proof must reach
  for n in [``Tools.ShippingMachineClosesData.letsClose_of_data, ``Tools.ShippingClosesSplit.machineCloses_iff,
      ``Tools.ShippingGen5Acc.machineClosesAtA_of_closes, ``Tools.ShippingGen5Acc.dataOf₀_of_genData₀] do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A7): {seen.toList.length} constants, no forbidden constant, 4 expected suppliers reached, no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccClosesCheck
