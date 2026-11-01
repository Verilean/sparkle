import Tools.ShippingGen5AccGDf
import Tests.Gen5.AccCheck
-- Pod incremental build OK (exit 0, 731 jobs): TYPE 6 (Pi 3 + theorems 3) / BODY 2 / MUTANT 5 (single 4 + compound 1; signature/defeq rejection, not semantic) / AXIOMS 6 standard / CLOSURE 6472 consts, unknown 0, suppliers GDEvidence/DataSoundAt. Clean issue-linked build: pending (coder). Check for A13, freeze scripts/gen5/DG_ACC_FREEZE_REV13.md §2.

/-! # DG-ACC unit A13 checks (Tools/ShippingGen5AccGDf.lean)

TYPE (Pi path): `getConstInfo c .type` against an independently written Pi type (`GDf`, `dOfF`, `genDataF`). TYPE (theorems): `checkExpected` against
independent `Expected...` statements. BODY (value path, counted apart): the VALUES of `GDf` and `dOfF` against independently written lambdas.
MUTANT: single and compound counted apart; signature / defeq rejection only, NOT a semantic counterexample. AXIOMS: standard three only
(`Classical.choice` is the only choice axiom, used by `genDataF`).
CLOSURE: explicit-value walker of `AccCheck`; forbidden `sorryAx / ofReduceBool / trustCompiler`; expected suppliers fixed (distinct from roots). -/
namespace Tests.Gen5.AccGDfCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)

section Expected

def ExpectedGDfType : Type 1 :=
  (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) → (env₀ : Lean.Environment) →
    (E : Lean.ConstantInfo) → Type

def ExpectedDOfFType : Type :=
  (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) → (env₀ : Lean.Environment) →
    {E : Lean.ConstantInfo} → (g : GDf f env₀ E) → MachineData

def ExpectedGenDataFType : Type :=
  (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) → (env₀ : Lean.Environment) →
    (E : Lean.ConstantInfo) → Option (GDf f env₀ E)

def ExpectedGDfBody : (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) → (env₀ : Lean.Environment) →
    (E : Lean.ConstantInfo) → Type :=
  fun f env₀ E => { p : MachineShape × MachineData //
    machineShape? false [] E (structEnv env₀) = some p.1 ∧ f E (structEnv env₀) p.1 = some p.2 ∧ p.2.shape = p.1 }

def ExpectedDOfFBody : (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) → (env₀ : Lean.Environment) →
    {E : Lean.ConstantInfo} → (g : GDf f env₀ E) → MachineData :=
  fun f env₀ {E} g => g.val.2

def ExpectedEvidence : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment),
    GDEvidence f (GDf f env₀) (fun {E} g => dOfF f env₀ g) env₀

def ExpectedIsSomeIff : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataF f env₀ E).isSome = true ↔
      ∃ (s : MachineShape) (d : MachineData),
        machineShape? false [] E (structEnv env₀) = some s ∧ f E (structEnv env₀) s = some d ∧ d.shape = s

def ExpectedIsSomeOfSound : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (hf : DataSoundAt f) (E : Lean.ConstantInfo) (s : MachineShape) (d : MachineData)
    (hs : machineShape? false [] E (structEnv env₀) = some s) (hd : f E (structEnv env₀) s = some d),
    (genDataF f env₀ E).isSome = true

-- single mutants
/-- (a) `d.shape = s` dropped from the right-hand side -/
def MutIffNoShape : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataF f env₀ E).isSome = true ↔
      ∃ (s : MachineShape) (d : MachineData),
        machineShape? false [] E (structEnv env₀) = some s ∧ f E (structEnv env₀) s = some d

/-- (b) forward direction only -/
def MutIffFwd : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataF f env₀ E).isSome = true →
      ∃ (s : MachineShape) (d : MachineData),
        machineShape? false [] E (structEnv env₀) = some s ∧ f E (structEnv env₀) s = some d ∧ d.shape = s

/-- (c) `hf` binder dropped -/
def MutSoundNoHf : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo) (s : MachineShape) (d : MachineData)
    (hs : machineShape? false [] E (structEnv env₀) = some s) (hd : f E (structEnv env₀) s = some d),
    (genDataF f env₀ E).isSome = true

/-- (d) evidence for the constant-`none` data function instead of `f` (modified statement) -/
def MutEvidenceNone : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment),
    GDEvidence (fun _ _ _ => none) (GDf f env₀) (fun {E} g => dOfF f env₀ g) env₀

-- compound mutant (two changes)
/-- (e) (a) AND (c) -/
def MutSoundNoHfNoShape : Prop :=
  ∀ (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo) (s : MachineShape) (d : MachineData)
    (hs : machineShape? false [] E (structEnv env₀) = some s) (hd : f E (structEnv env₀) s = some d),
    (genDataF f env₀ E).isSome = true ∧ d.shape = s

end Expected

/-- Compare the TYPE (Pi type) of a constant with the VALUE of an independent `def ... : Type`. -/
def checkTypeOfConst (c exp : Name) : MetaM Unit := do
  let a := (← getConstInfo c).type
  let e ← stmtOf exp
  cmpTele s!"{c} (Pi type)" a e
  logInfo m!"GEN5 TYPE(Pi) OK {c} against {exp}"

/-- BODY: the VALUE of `c` against the VALUE of the independent definition. -/
def checkBody (c exp : Name) : MetaM Unit := do
  cmpTele s!"{c} (body)" (← stmtOf c) (← stmtOf exp)
  logInfo m!"GEN5 BODY OK {c} against {exp}"

/-- BODY mutant: the value of `c` must NOT match the mutant's value (signature/defeq rejection). -/
def checkBodyMutant (c mt : Name) : MetaM Unit := do
  let a ← stmtOf c
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try cmpTele s!"{c} vs body mutant {mt}" a e; pure true catch _ => pure false
  if accepted then throwError "GEN5 MUTANT ACCEPTED: {mt} matches the body of {c}"
  if (← withoutModifyingState (isDefEq a e)) then throwError "GEN5 MUTANT ACCEPTED (isDefEq): {mt} vs the body of {c}"
  logInfo m!"GEN5 MUTANT(BODY path) REJECTED {mt} (against the value of {c})"

run_cmd Lean.Elab.Command.liftTermElabM do
  -- TYPE: 3 Pi + 3 theorems
  checkTypeOfConst ``GDf ``ExpectedGDfType
  checkTypeOfConst ``dOfF ``ExpectedDOfFType
  checkTypeOfConst ``genDataF ``ExpectedGenDataFType
  checkExpected ``genDataF_evidence ``ExpectedEvidence
  checkExpected ``genDataF_isSome_iff ``ExpectedIsSomeIff
  checkExpected ``genDataF_isSome_of_sound ``ExpectedIsSomeOfSound
  -- BODY: 2
  checkBody ``GDf ``ExpectedGDfBody
  checkBody ``dOfF ``ExpectedDOfFBody
  -- MUTANT single: 4
  checkMutant ``genDataF_isSome_iff ``MutIffNoShape
  checkMutant ``genDataF_isSome_iff ``MutIffFwd
  checkMutant ``genDataF_isSome_of_sound ``MutSoundNoHf
  checkMutant ``genDataF_evidence ``MutEvidenceNone
  -- MUTANT compound: 1
  checkMutant ``genDataF_isSome_of_sound ``MutSoundNoHfNoShape
  logInfo m!"GEN5 A13 COUNTS: TYPE 6 (Pi 3 + theorems 3) / BODY 2 / MUTANT 5 (single 4 + compound 1)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``GDf
  checkAxioms ``dOfF
  checkAxioms ``genDataF
  checkAxioms ``genDataF_evidence
  checkAxioms ``genDataF_isSome_iff
  checkAxioms ``genDataF_isSome_of_sound

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
  let roots := [``GDf, ``dOfF, ``genDataF, ``genDataF_evidence, ``genDataF_isSome_iff, ``genDataF_isSome_of_sound]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  let suppliers := [``Tools.ShippingGen5Acc.GDEvidence, ``Tools.ShippingGen5Acc.DataSoundAt]
  for n in suppliers do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A13): {seen.toList.length} constants, no forbidden constant, expected suppliers GDEvidence/DataSoundAt reached (distinct from the 6 roots), no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccGDfCheck
