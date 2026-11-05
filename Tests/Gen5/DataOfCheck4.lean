import Tools.ShippingGen5DataOfDims
import Tests.Gen5.DataOfCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT by an issue-linked clean build (agent build: Tools.ShippingGen5DataOfDims 365 jobs, Tests.Gen5.DataOfCheck4 762 jobs, exit 0; the clean build is the coder's). No sorry / axiom / native_decide.
-- (DG-DATAOF checks for Tools/ShippingGen5DataOfDims.lean; scripts/gen5/DG_DATAOF_FREEZE.md rev3 §10.)

/-! # DG-DATAOF row 6b checks

1. TYPE: statements against independently written `Prop`s (the four `d`-side premises of DG-COVER's `shapeAgree_of_sides`
   as read from `kjob/g5cv-r11 9b9cdd55` `Tools/ShippingGen5Cover5.lean`, not copied from the Lean statements here).
2. MUTANT: single changes / dropped conjuncts are rejected by the SAME comparison (signature / defeq rejections, NOT semantic counterexamples).
3. Value closure by the common `Tests.Gen5.DataOfCheck.reach` (unknown names fail). 4. Axioms.
Not checked: that `dataOfAt` is `some`, that `s` is the run's `sp`, row 6a. -/

namespace Tests.Gen5.DataOfCheck4
open Lean Meta
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingGen5DataOfPure Tools.ShippingGen5DataOf
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.Compiler.Elab
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types -/

def ExpFromDims : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn

def ExpAtDims : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData},
    ∀ (h : dataOfAt lvl E senv s = some d),
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn

def ExpFromNIn : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    ∃ p, mixedGatePeel tin = some p ∧ d.nIn = p.1.length + s.insts.length

def ExpFromSoundDims : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    (d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom
        (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
      d.initOk (initsOf d) = true) ∧
    (d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn)

def ExpAtSoundDims : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData},
    ∀ (h : dataOfAt lvl E senv s = some d),
    (d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom
        (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
      d.initOk (initsOf d) = true) ∧
    (d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn)

def ExpTypedLen : Prop :=
  ∀ {ks : List MixedGateBinder} {fs : List (Σ w : Nat, Term (.bits w))} {r : List (Σ s : SType, Term s)},
    ∀ (h : typedFields ks fs = some r), r.length = min ks.length fs.length

def ExpFrontSome : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape} {tin : Lean.Expr}
    {fl : Lean.Expr → Lean.Expr} {nIn : Nat} {dom : Lean.Expr},
    ∀ (h : dataOfFront E senv shape tin fl = some (nIn, dom)),
    (∃ p, mixedGatePeel tin = some p ∧ nIn = p.1.length + shape.insts.length) ∧
    shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets

def ExpCoreDims : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {d : MachineData},
    ∀ (hb : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
      (h : dataOfCore lvl shape nIn dom = some d),
    d.shape = shape ∧ d.nIn = nIn ∧ d.ss.length = shape.layout.slots.length ∧ d.ls.length = shape.layout.lets

/-! ## 2. Mutants -/

def MutSsLsSwapped : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ls.length = s.layout.slots.length ∧ d.ss.length = s.layout.lets ∧ s.insts.length ≤ d.nIn

def MutStrictNIn : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length < d.nIn

def MutLsOuts : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.outs.length ∧ s.insts.length ≤ d.nIn

def MutNoShape : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn

def MutAtNoNIn : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData},
    ∀ (h : dataOfAt lvl E senv s = some d),
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets

def MutSoundOnly : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    (d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom
        (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
      d.initOk (initsOf d) = true)

def MutTypedLenMax : Prop :=
  ∀ {ks : List MixedGateBinder} {fs : List (Σ w : Nat, Term (.bits w))} {r : List (Σ s : SType, Term s)},
    ∀ (h : typedFields ks fs = some r), r.length = max ks.length fs.length

def MutCoreNoHyp : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {d : MachineData},
    ∀ (h : dataOfCore lvl shape nIn dom = some d),
    d.shape = shape ∧ d.nIn = nIn ∧ d.ss.length = shape.layout.slots.length ∧ d.ls.length = shape.layout.lets

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``dataOfFrom_dims ``ExpFromDims
  checkExpected ``dataOfAt_dims ``ExpAtDims
  checkExpected ``dataOfFrom_nIn ``ExpFromNIn
  checkExpected ``dataOfFrom_sound_dims ``ExpFromSoundDims
  checkExpected ``dataOfAt_sound_dims ``ExpAtSoundDims
  checkExpected ``typedFields_length ``ExpTypedLen
  checkExpected ``dataOfFront_some ``ExpFrontSome
  checkExpected ``dataOfCore_dims ``ExpCoreDims
  checkMutant ``dataOfFrom_dims ``MutSsLsSwapped
  checkMutant ``dataOfFrom_dims ``MutStrictNIn
  checkMutant ``dataOfFrom_dims ``MutLsOuts
  checkMutant ``dataOfFrom_dims ``MutNoShape
  checkMutant ``dataOfAt_dims ``MutAtNoNIn
  checkMutant ``dataOfFrom_sound_dims ``MutSoundOnly
  checkMutant ``typedFields_length ``MutTypedLenMax
  checkMutant ``dataOfCore_dims ``MutCoreNoHyp

/-! ## 3. Value closure -/

open Tests.Gen5.DataOfCheck in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  unless badProj (.proj `Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "DATAOF4 AUDIT FAILED: raw T1Hyp proj missed"
  let F := `Tests.Gen5.DataOfFixture
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badNDCases, true), (F ++ `badEqual, true), (F ++ `unrelated, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "DATAOF4 AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "DATAOF4 AUDIT FAILED: detector flags {c}"
    logInfo m!"DATAOF4 CONTROL {c}: {toString r.hit}"
  for c in [``dataOfFrom_dims, ``dataOfAt_dims, ``dataOfFrom_nIn, ``dataOfFrom_sound_dims, ``dataOfAt_sound_dims,
      ``typedFields_length, ``dataOfFront_some, ``dataOfCore_dims, ``dataOfTail_dims, ``mapM_unField_length] do
    let r ← reach c
    if let some p := r.hit then throwError "DATAOF4 AUDIT FAILED {c}: forbidden use via {p}"
    logInfo m!"DATAOF4 REACH {c}: no T1Hyp / T1HypND / Expr.equal / Expr.eqv / ofReduceBool; visited {r.visited}, body-less {r.noBody}, opaque {r.opaques} {r.opaqueNames}"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``dataOfFrom_dims, ``dataOfAt_dims, ``dataOfFrom_nIn, ``dataOfFrom_sound_dims, ``dataOfAt_sound_dims,
      ``typedFields_length, ``dataOfFront_some, ``dataOfCore_dims, ``dataOfTail_dims] do
    checkAxioms n

end Tests.Gen5.DataOfCheck4
