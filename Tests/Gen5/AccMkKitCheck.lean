import Tools.ShippingGen5AccMkKit
import Tests.Gen5.AccCheck
-- Pod incremental build OK at 74a2e66c (exit 0, 729 jobs): TYPE 4 (Pi 1 + theorems 3) / BODY 1 / MUTANT 6 (single 5 + compound 1; signature/defeq rejection, not semantic) / AXIOMS 4 standard / CLOSURE 6583 consts, unknown 0. Clean build not yet run. (Check for A11, freeze scripts/gen5/DG_ACC_FREEZE_REV11.md §2 as revised at 8e0d0bc3).

/-! # DG-ACC unit A11 checks (Tools/ShippingGen5AccMkKit.lean)

TYPE (Pi path): the type of `mkKit` recorded in the environment (`getConstInfo ``mkKit` `.type`) against an independently written Pi type
`ExpectedMkKitType`. TYPE (theorems): `checkExpected` against independently written `Expected...` statements. BODY (value path): the VALUE of
`mkKit` against an independently written structure literal `ExpectedMkKitBody`; counted apart from TYPE.
MUTANT: single and compound counted apart; each is a well-typed Pi type or a statement built from the real `mkKit` arguments; rejected by
signature / defeq, NOT a semantic counterexample. AXIOMS: standard three only. CLOSURE: explicit-value walker of `AccCheck`; forbidden
`sorryAx / ofReduceBool / trustCompiler`; expected suppliers fixed (reached constants, distinct from the roots). -/
namespace Tests.Gen5.AccMkKitCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)

section Expected

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}

-- independent Pi type of `mkKit` (written from the freeze §1 binders)
def ExpectedMkKitType : Type 1 :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    AssignKit ι dom env₀

-- independent structure literal for the body of `mkKit`
def ExpectedMkKitBody
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g) :
    AssignKit ι dom env₀ :=
  { dataOf := f, GD := GD, dOf := dOf, genData₀ := genData₀, ordCallees := ordCallees, genSem := genSem,
    mem_ordCallees := hmem,
    genData₀_dataOf := genData₀_dataOf_of_evidence f GD dOf genData₀ hev,
    genSem_local := hloc, genSem_decl := hdecl, genSem_d := hd }

def ExpectedDataOf : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    ((mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd)).dataOf = f

def ExpectedAgrees : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    KitAgrees (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) f

def ExpectedDataSound : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : DataSoundAt f),
    DataSound (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd)

-- single-change mutants
/-- Pi type of `mkKit` without `hev` (TYPE path) -/
def MutTypeNoHev : Type 1 :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    AssignKit ι dom env₀

/-- Pi type of `mkKit` without `hloc` (TYPE path) -/
def MutTypeNoHloc : Type 1 :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    AssignKit ι dom env₀

/-- `mkKit_agrees` for a different function `g` (the kit is the real `mkKit f ..`) -/
def MutAgreesOtherFn : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (g : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData),
    KitAgrees (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) g

/-- `mkKit_dataSound` without the `hf` binder -/
def MutDataSoundNoHf : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g),
    DataSound (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd)

/-- `mkKit_dataSound` with `hf` weakened to `d.ok = true` only (all `mkKit` arguments and the conclusion kept) -/
def MutDataSoundWeakHf : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), f E se s = some d → d.ok = true),
    DataSound (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd)

-- compound mutant (two changes)
/-- `hf` weakened as above AND the conclusion changed to `KitAgrees (mkKit ..) f` -/
def MutDataSoundCompound : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (f : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (GD : Lean.ConstantInfo → Type) (dOf : {E : Lean.ConstantInfo} → GD E → MachineData)
    (genData₀ : (E : Lean.ConstantInfo) → Option (GD E))
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : Lean.ConstantInfo} → GD E → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence f GD dOf env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E),
      (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (g : GD E), (genSem Q X g).d = dOf g)
    (hf : ∀ (E : Lean.ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), f E se s = some d → d.ok = true),
    KitAgrees (mkKit f GD dOf genData₀ ordCallees genSem hmem hev hloc hdecl hd) f

end Expected

/-- Compare the TYPE (Pi type) of a constant with the VALUE of an independent `def ... : Type 1`. -/
def checkTypeOfConst (c exp : Name) : MetaM Unit := do
  let a := (← getConstInfo c).type
  let e ← stmtOf exp
  cmpTele s!"{c} (Pi type)" a e
  logInfo m!"GEN5 TYPE(Pi) OK {c} against {exp}"

def checkMutantType (c mt : Name) : MetaM Unit := do
  let a := (← getConstInfo c).type
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try cmpTele s!"{c} vs mutant {mt}" a e; pure true catch _ => pure false
  if accepted then throwError "GEN5 MUTANT ACCEPTED: {mt} matches the type of {c}"
  if (← withoutModifyingState (isDefEq a e)) then throwError "GEN5 MUTANT ACCEPTED (isDefEq): {mt} vs the type of {c}"
  logInfo m!"GEN5 MUTANT(TYPE path) REJECTED {mt} (against the type of {c})"

/-- BODY: the VALUE of `mkKit` against the VALUE of the independent structure literal. -/
def checkBody (c exp : Name) : MetaM Unit := do
  cmpTele s!"{c} (body)" (← stmtOf c) (← stmtOf exp)
  logInfo m!"GEN5 BODY OK {c} against {exp}"

run_cmd Lean.Elab.Command.liftTermElabM do
  -- TYPE: 1 Pi (mkKit) + 3 theorems
  checkTypeOfConst ``mkKit ``ExpectedMkKitType
  checkExpected ``mkKit_dataOf ``ExpectedDataOf
  checkExpected ``mkKit_agrees ``ExpectedAgrees
  checkExpected ``mkKit_dataSound ``ExpectedDataSound
  -- BODY: 1
  checkBody ``mkKit ``ExpectedMkKitBody
  -- MUTANT single: 5 (2 on the TYPE path, 3 on theorem statements)
  checkMutantType ``mkKit ``MutTypeNoHev
  checkMutantType ``mkKit ``MutTypeNoHloc
  checkMutant ``mkKit_agrees ``MutAgreesOtherFn
  checkMutant ``mkKit_dataSound ``MutDataSoundNoHf
  checkMutant ``mkKit_dataSound ``MutDataSoundWeakHf
  -- MUTANT compound: 1
  checkMutant ``mkKit_dataSound ``MutDataSoundCompound
  logInfo m!"GEN5 A11 COUNTS: TYPE 4 (Pi 1 + theorems 3) / BODY 1 / MUTANT 6 (single 5 + compound 1)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``mkKit
  checkAxioms ``mkKit_dataOf
  checkAxioms ``mkKit_agrees
  checkAxioms ``mkKit_dataSound

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
  let roots := [``mkKit, ``mkKit_dataOf, ``mkKit_agrees, ``mkKit_dataSound]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  let suppliers := [``Tools.ShippingGen5Acc.genData₀_dataOf_of_evidence, ``Tools.ShippingGen5Acc.kitAgrees_of_eq,
    ``Tools.ShippingGen5Acc.dataSound_of_agree, ``Tools.ShippingGen5Acc.AssignKit]
  for n in suppliers do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A11): {seen.toList.length} constants, no forbidden constant, expected suppliers reached (distinct from the 4 roots), no excluded supplier-unit constant, no unknown constant"

end Tests.Gen5.AccMkKitCheck
