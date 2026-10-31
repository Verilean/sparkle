import Tools.ShippingGen5AccDataAgree
import Tests.Gen5.AccCheck
-- Clean issue-linked build ac18v-7076f718 (approved at 7076f718), exit 0, 727 jobs, dirty=false: TYPE 3 (2 definitions by body + 1 theorem) / MUTANT 6 (signature/defeq rejection, not semantic): 5 single-change + 1 COMPOUND (MutCompoundShape) / AXIOMS 1 standard three only / CLOSURE OK 3783 constants (unknown 0; the '3 expected suppliers reached' is the union of the 3 roots, two of which (DataSoundAt, KitAgrees) are roots themselves, so it is NOT an independent proof-dependency assert; DataOf/SemGen units not reached) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. Sorry warnings are the walker-control negatives only.

/-! # DG-ACC unit A9 checks (Tools/ShippingGen5AccDataAgree.lean; scripts/gen5/DG_ACC_FREEZE_REV9.md §2)

TYPE: `DataSoundAt`, `KitAgrees` (compared by BODY) and `dataSound_of_agree`, binder by binder (`checkExpected`) with independently written `Expected…`
statements (from the prose of REV9 §1: spec of a plain function; pointwise agreement of the kit's `dataOf` with it).
MUTANT: well-typed changes, SINGLE (one place changed) and COMPOUND (several places) counted apart, each compared with the same comparator and
required to be rejected -- a rejection by signature / defeq, NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: explicit-value walker of `AccCheck`; forbidden set `sorryAx / ofReduceBool / trustCompiler`; expected suppliers
fixed; the excluded supplier units (`ShippingGen5DataOf*`, `ShippingGen5SemGen*`) must not be reached. -/
namespace Tests.Gen5.AccDataAgreeCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMixedSourceBridge (inputExpr)

section Expected

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

-- every result of `f`: its shape is the asked shape, it passes ok, its body is the quotation of the packed term
def ExpectedSoundAt (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), f E se s = some d →
    d.shape = s ∧ d.ok = true ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)

-- the kit's dataOf equals f at every point
def ExpectedAgrees (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape), K.dataOf E se s = f E se s

def ExpectedAgreeThm : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData),
    (hf : DataSoundAt f) → (hK : KitAgrees K f) → DataSound K

-- single-change mutants (each well-typed; signature/defeq rejection only)
/-- `DataSoundAt` without the body equation -/
def MutAtNoBody (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), f E se s = some d →
    d.shape = s ∧ d.ok = true

/-- `DataSoundAt` without `d.ok` -/
def MutAtNoOk (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), f E se s = some d →
    d.shape = s ∧
      (d.shape.body = Tools.ShippingUnifiedSource.quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)

/-- `KitAgrees` with the equation flipped -/
def MutAgreesFlip (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop :=
  ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape), f E se s = K.dataOf E se s

/-- `dataSound_of_agree` without `hf` -/
def MutNoHf : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData),
    (hK : KitAgrees K f) → DataSound K

/-- `dataSound_of_agree` without `hK` -/
def MutNoHK : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData),
    (hf : DataSoundAt f) → DataSound K

-- compound mutant (more than one place changed)
/-- conclusion `DataOfShape K` AND `hf` weakened to the shape conjunct -/
def MutCompoundShape : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData),
    (hf : ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData),
      f E se s = some d → d.shape = s) → (hK : KitAgrees K f) → DataOfShape K

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``DataSoundAt ``ExpectedSoundAt
  checkExpected ``KitAgrees ``ExpectedAgrees
  checkExpected ``dataSound_of_agree ``ExpectedAgreeThm
  -- single-change mutants: 5
  checkMutant ``DataSoundAt ``MutAtNoBody
  checkMutant ``DataSoundAt ``MutAtNoOk
  checkMutant ``KitAgrees ``MutAgreesFlip
  checkMutant ``dataSound_of_agree ``MutNoHf
  checkMutant ``dataSound_of_agree ``MutNoHK
  -- compound mutant: 1
  checkMutant ``dataSound_of_agree ``MutCompoundShape

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``dataSound_of_agree

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
  let roots := [``DataSoundAt, ``KitAgrees, ``dataSound_of_agree]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  -- the 3 roots' union (DataSoundAt and KitAgrees are roots themselves; not an independent proof-dependency assert)
  for n in [``Tools.ShippingGen5Acc.DataSound, ``Tools.ShippingGen5Acc.KitAgrees, ``Tools.ShippingGen5Acc.DataSoundAt] do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A9): {seen.toList.length} constants, no forbidden constant, 3 expected suppliers reached, no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccDataAgreeCheck
