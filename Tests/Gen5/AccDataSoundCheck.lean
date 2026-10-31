import Tools.ShippingGen5AccDataSound
import Tests.Gen5.AccCheck
-- NOT BUILT (A8, g5ac-r16): Check build not yet recorded; the clean issue-linked build is the coder's. No sorry / axiom / native_decide in this source; the sorry warnings of a build are the intended walker-control negatives (the `walkerControls` line).

/-! # DG-ACC unit A8 checks (Tools/ShippingGen5AccDataSound.lean; scripts/gen5/DG_ACC_FREEZE_REV8.md §2)

TYPE: `DataSound` (compared by BODY) and the two theorems, binder by binder (`checkExpected`) with independently written `Expected…`
statements (from the prose of REV8 §1: kit results carry shape equality, `ok`, and the body equation; transport to reached names).
MUTANT: one-place, well-typed changes compared with the same comparator and required to be rejected -- a rejection by signature / defeq,
NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: explicit-value walker of `AccCheck`; forbidden set `sorryAx / ofReduceBool / trustCompiler`; expected suppliers
fixed; the excluded supplier units (`ShippingGen5DataOf*`, `ShippingGen5SemGen*`) must not be reached. -/
namespace Tests.Gen5.AccDataSoundCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMixedSourceBridge (inputExpr)

section Expected

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

-- every result of the kit's dataOf: its shape is the asked shape, it passes ok, its body is the quotation of the packed term
def ExpectedSound (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d →
    d.shape = s ∧ d.ok = true ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)

def ExpectedShapeThm : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀),
    (h : DataSound K) → DataOfShape K

def ExpectedClosesThm : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (Reach : Name → Prop), (h : DataSound K) →
    (hL : ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d → d.letsAliasOk = true) → ClosesData K Reach

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `DataSound` without the body equation -/
def MutSoundNoBody (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d →
    d.shape = s ∧ d.ok = true

/-- `DataSound` without `d.ok` -/
def MutSoundNoOk (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d →
    d.shape = s ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)

/-- `DataSound` without `d.shape = s` -/
def MutSoundNoShape (K : AssignKit ι dom env₀) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d →
    d.ok = true ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)

/-- `closesData_of_sound` without `hL` -/
def MutNoHL : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (Reach : Name → Prop), (h : DataSound K) → ClosesData K Reach

/-- `closesData_of_sound` without `h` -/
def MutNoH : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (Reach : Name → Prop),
    (hL : ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d → d.letsAliasOk = true) → ClosesData K Reach

/-- `dataOfShape_of_sound` with a `Reach`-restricted statement -/
def MutShapeReach : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (Reach : Name → Prop), (h : DataSound K) →
    ∀ (c : Name) (d : MachineData), Reach c → dataOf₀ K c = some d → d.shape = d.shape

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``DataSound ``ExpectedSound
  checkExpected ``dataOfShape_of_sound ``ExpectedShapeThm
  checkExpected ``closesData_of_sound ``ExpectedClosesThm
  checkMutant ``DataSound ``MutSoundNoBody
  checkMutant ``DataSound ``MutSoundNoOk
  checkMutant ``DataSound ``MutSoundNoShape
  checkMutant ``closesData_of_sound ``MutNoHL
  checkMutant ``closesData_of_sound ``MutNoH
  checkMutant ``dataOfShape_of_sound ``MutShapeReach

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``dataOfShape_of_sound
  checkAxioms ``closesData_of_sound

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
  let roots := [``DataSound, ``dataOfShape_of_sound, ``closesData_of_sound]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  -- expected suppliers that the proofs must reach
  for n in [``Option.bind_eq_some_iff, ``Tools.ShippingGen5Acc.dataOf₀, ``Tools.ShippingGen5Acc.ClosesData,
      ``Tools.ShippingGen5Acc.DataOfShape] do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A8): {seen.toList.length} constants, no forbidden constant, 4 expected suppliers reached, no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccDataSoundCheck
