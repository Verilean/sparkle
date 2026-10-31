import Tools.ShippingGen5AccOrdCallees
import Tests.Gen5.AccCheck
-- Pod incremental build OK at b835726d (exit 0, 730 jobs): TYPE 3 (Pi 1 + theorems 2) / BODY 1 / MUTANT 5 (single 4 + compound 1; signature/defeq rejection, not semantic) / AXIOMS 3 standard / CLOSURE 6664 consts, unknown 0. Clean issue-linked build pending (coder). Check for A12, freeze scripts/gen5/DG_ACC_FREEZE_REV12.md §2.

/-! # DG-ACC unit A12 checks (Tools/ShippingGen5AccOrdCallees.lean)

TYPE (Pi path): `getConstInfo ``ordCallees₀` `.type` against an independently written Pi type. TYPE (theorems): `checkExpected` against
independent `Expected...` statements. BODY (value path, counted apart): the VALUE of `ordCallees₀` against an independently written lambda.
MUTANT: single and compound counted apart; signature / defeq rejection only, NOT a semantic counterexample. AXIOMS: standard three only.
CLOSURE: explicit-value walker of `AccCheck`; forbidden `sorryAx / ofReduceBool / trustCompiler`; expected suppliers fixed (distinct from roots). -/
namespace Tests.Gen5.AccOrdCalleesCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)

section Expected

def ExpectedOrdCalleesType : Type :=
  (d : MachineData) → List (Fin d.shape.insts.length)

def ExpectedOrdCalleesBody : (d : MachineData) → List (Fin d.shape.insts.length) :=
  fun d => (List.finRange d.shape.insts.length).filter
    (fun k => ((d.shape.instOrigins.getD k .ord).child?).isNone)

def ExpectedMem : Prop :=
  ∀ (d : MachineData) (k : Fin d.shape.insts.length),
    k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? = none

def ExpectedDataSound : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees₀ (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : DataSoundAt f),
    DataSound (mkKit f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd)

-- single mutants
/-- (a) `child? ≠ none` in place of `= none` -/
def MutMemNe : Prop :=
  ∀ (d : MachineData) (k : Fin d.shape.insts.length),
    k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? ≠ none

/-- (b) forward direction only -/
def MutMemFwd : Prop :=
  ∀ (d : MachineData) (k : Fin d.shape.insts.length),
    k ∈ ordCallees₀ d → (d.shape.instOrigins.getD k .ord).child? = none

/-- (c) `hf` binder dropped (all other binders and the conclusion kept) -/
def MutDataSoundNoHf : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees₀ (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    DataSound (mkKit f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd)

/-- (d) value mutant (BODY path): filter on `isSome` instead of `isNone` -/
def MutBodyIsSome : (d : MachineData) → List (Fin d.shape.insts.length) :=
  fun d => (List.finRange d.shape.insts.length).filter
    (fun k => ((d.shape.instOrigins.getD k .ord).child?).isSome)

-- compound mutant (two changes)
/-- (e) `child? ≠ none` AND forward direction only -/
def MutMemCompound : Prop :=
  ∀ (d : MachineData) (k : Fin d.shape.insts.length),
    k ∈ ordCallees₀ d → (d.shape.instOrigins.getD k .ord).child? ≠ none

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
  -- TYPE: 1 Pi (ordCallees₀) + 2 theorems
  checkTypeOfConst ``ordCallees₀ ``ExpectedOrdCalleesType
  checkExpected ``ordCallees₀_mem ``ExpectedMem
  checkExpected ``mkKit_ordCallees₀_dataSound ``ExpectedDataSound
  -- BODY: 1
  checkBody ``ordCallees₀ ``ExpectedOrdCalleesBody
  -- MUTANT single: 4 (3 theorem statements, 1 body)
  checkMutant ``ordCallees₀_mem ``MutMemNe
  checkMutant ``ordCallees₀_mem ``MutMemFwd
  checkMutant ``mkKit_ordCallees₀_dataSound ``MutDataSoundNoHf
  checkBodyMutant ``ordCallees₀ ``MutBodyIsSome
  -- MUTANT compound: 1
  checkMutant ``ordCallees₀_mem ``MutMemCompound
  logInfo m!"GEN5 A12 COUNTS: TYPE 3 (Pi 1 + theorems 2) / BODY 1 / MUTANT 5 (single 4 + compound 1)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``ordCallees₀
  checkAxioms ``ordCallees₀_mem
  checkAxioms ``mkKit_ordCallees₀_dataSound

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
  let roots := [``ordCallees₀, ``ordCallees₀_mem, ``mkKit_ordCallees₀_dataSound]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  let suppliers := [``Tools.ShippingGen5Acc.mkKit_dataSound, ``Tools.ShippingGen5Acc.mkKit]
  for n in suppliers do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A12): {seen.toList.length} constants, no forbidden constant, expected suppliers reached (distinct from the 3 roots), no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccOrdCalleesCheck
