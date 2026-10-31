import Tools.ShippingGen5AccGenDataEv
import Tests.Gen5.AccCheck
-- Clean issue-linked build ac20v-1e791651 (approved at 1e791651; Lean source unchanged since 6b94f3b4), exit 0, 728 jobs, dirty=false: TYPE 3 (1 definition by body + 2 theorems) / MUTANT 5 (signature/defeq rejection, not semantic): 4 single-change + 1 COMPOUND / AXIOMS 2 theorems standard three only / CLOSURE OK 6232 constants (unknown 0; roots GDEvidence, genData₀_dataOf_of_evidence, kitAgrees_of_eq; KitAgrees/AssignKit reached and distinct from the roots; DataOf/SemGen units not reached) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. Sorry warnings are the walker-control negatives only. Compound mutant: the freeze rev10 text proposed a `.map` form for the conclusion; the implementation uses the `isSome` form (`(machineShape? ..).isSome = true`) together with `hev` weakened to the shape conjunct. The 4 single-change mutants are as frozen. All mutants are rejected by signature/defeq, not semantic counterexamples.

/-! # DG-ACC unit A10 checks (Tools/ShippingGen5AccGenDataEv.lean; scripts/gen5/DG_ACC_FREEZE_REV10.md §2)

TYPE: `GDEvidence` (compared by BODY) and the two theorems, binder by binder (`checkExpected`) with independently written `Expected...`
statements (from the prose of REV10 §1). MUTANT: well-typed changes, SINGLE and COMPOUND counted apart, each required to be rejected -- a
rejection by signature / defeq, NOT a semantic counterexample. AXIOMS: standard three only. CLOSURE: explicit-value walker of `AccCheck`;
forbidden set `sorryAx / ofReduceBool / trustCompiler`; expected suppliers fixed (a union of the roots; `KitAgrees` / `AssignKit` are reached
constants distinct from the roots `GDEvidence`, `genData₀_dataOf_of_evidence`, `kitAgrees_of_eq`); the excluded supplier units must not be reached. -/
namespace Tests.Gen5.AccGenDataEvCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)

section Expected

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

-- every replacement point: the shape of the entry is the point's shape, and dataOf at that shape returns the point's data
def ExpectedEvidence (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData) (env₀ : Lean.Environment) : Prop :=
  ∀ (E : Lean.ConstantInfo) (g : GD E),
    machineShape? false [] E (structEnv env₀) = some (dOf g).shape ∧
    dataOf E (structEnv env₀) (dOf g).shape = some (dOf g)

def ExpectedEvThm : Prop :=
  ∀ {env₀ : Lean.Environment} (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E)),
    (hev : GDEvidence dataOf GD dOf env₀) →
    ∀ {E : Lean.ConstantInfo} {g : GD E}, genData₀ E = some g →
      ((machineShape? false [] E (structEnv env₀)).bind (dataOf E (structEnv env₀))) = some (dOf g)

def ExpectedKitEq : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment} (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (h : K.dataOf = f), KitAgrees K f

-- single-change mutants (each well-typed; signature/defeq rejection only)
/-- `GDEvidence` without the `hdata` conjunct -/
def MutEvNoData (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData) (env₀ : Lean.Environment) : Prop :=
  ∀ (E : Lean.ConstantInfo) (g : GD E),
    machineShape? false [] E (structEnv env₀) = some (dOf g).shape

/-- `GDEvidence` with the `machineShape?` flag `true` -/
def MutEvFlag (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData) (env₀ : Lean.Environment) : Prop :=
  ∀ (E : Lean.ConstantInfo) (g : GD E),
    machineShape? true [] E (structEnv env₀) = some (dOf g).shape ∧
    dataOf E (structEnv env₀) (dOf g).shape = some (dOf g)

/-- `kitAgrees_of_eq` without `h` -/
def MutKitNoH : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment} (K : AssignKit ι dom env₀)
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData), KitAgrees K f

/-- `genData₀_dataOf_of_evidence` without `hev` -/
def MutEvThmNoHev : Prop :=
  ∀ {env₀ : Lean.Environment} (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E)),
    ∀ {E : Lean.ConstantInfo} {g : GD E}, genData₀ E = some g →
      ((machineShape? false [] E (structEnv env₀)).bind (dataOf E (structEnv env₀))) = some (dOf g)

-- compound mutant (more than one place changed)
/-- `hev` weakened to the shape conjunct AND the conclusion replaced by `isSome` of the shape -/
def MutEvThmCompound : Prop :=
  ∀ {env₀ : Lean.Environment} (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E)),
    (∀ (E : Lean.ConstantInfo) (g : GD E), machineShape? false [] E (structEnv env₀) = some (dOf g).shape) →
    ∀ {E : Lean.ConstantInfo} {g : GD E}, genData₀ E = some g →
      (machineShape? false [] E (structEnv env₀)).isSome = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``GDEvidence ``ExpectedEvidence
  checkExpected ``genData₀_dataOf_of_evidence ``ExpectedEvThm
  checkExpected ``kitAgrees_of_eq ``ExpectedKitEq
  -- single-change mutants: 4
  checkMutant ``GDEvidence ``MutEvNoData
  checkMutant ``GDEvidence ``MutEvFlag
  checkMutant ``kitAgrees_of_eq ``MutKitNoH
  checkMutant ``genData₀_dataOf_of_evidence ``MutEvThmNoHev
  -- compound mutant: 1
  checkMutant ``genData₀_dataOf_of_evidence ``MutEvThmCompound

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``genData₀_dataOf_of_evidence
  checkAxioms ``kitAgrees_of_eq

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
  let roots := [``GDEvidence, ``genData₀_dataOf_of_evidence, ``kitAgrees_of_eq]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  -- expected suppliers: reached constants distinct from the roots (`KitAgrees`'s statement mentions `AssignKit.dataOf`)
  for n in [``Tools.ShippingGen5Acc.KitAgrees, ``Tools.ShippingGen5Acc.AssignKit, ``Tools.ShippingGen5Acc.AssignKit.dataOf] do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
  for n in [``Tools.ShippingGen5Acc.KitAgrees, ``Tools.ShippingGen5Acc.AssignKit] do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A10): {seen.toList.length} constants, no forbidden constant, expected suppliers KitAgrees / AssignKit reached (distinct from the 3 roots), no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccGenDataEvCheck
