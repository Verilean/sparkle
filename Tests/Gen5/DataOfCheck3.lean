import Tools.ShippingGen5DataOf
import Tests.Gen5.DataOfCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT by an issue-linked clean build (DG-DATAOF checks for Tools/ShippingGen5DataOf.lean; scripts/gen5/DG_DATAOF_FREEZE.md rev2 Q5).
-- No sorry / axiom / native_decide.

/-! # DG-DATAOF checks for `dataOfFrom` / `dataOfAt` and their conditional soundness

1. TYPE: the theorem statements and the `def` signatures against independently written expected types.
2. MUTANT: well-typed one-point changes of the soundness statement are rejected by the SAME comparison
   (signature / defeq rejections, NOT semantic counterexamples).
3. Kernel controls on the small total pieces (`typedFields` does not check a `.bits n` width: the width comes from `ok`).
4. Value closure: explicit walk (`Tests.Gen5.DataOfCheck.reach`) with the detector's own controls re-run here;
   opaque / body-less constants are counted, their bodies are NOT explored (`packTupleInputs`, `rootFloat` are `partial`).
5. Axioms.

Not checked here (not supplied): that `dataOfAt` is `some` on any run, `tin`/`fl` agree with the compiler's values,
agreement with `readMachine`, C-CMP / C-QWIT, `dataOf` at `exprSize`. `GENFACTS`/SEM/COVER are not defined here. -/

namespace Tests.Gen5.DataOfCheck3
open Lean Meta
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingGen5DataOfPure Tools.ShippingGen5DataOf
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.Compiler.Elab
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types -/

def ExpDataOfFromSound : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

def ExpDataOfAtSound : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData},
    ∀ (h : dataOfAt lvl E senv s = some d),
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

def ExpDataOfCoreSound : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {d : MachineData},
    ∀ (h : dataOfCore lvl shape nIn dom = some d),
    d.shape = shape ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

def ExpCheckedSound : Prop :=
  ∀ {W : Nat} {whole : Term (.bits W)} {d d' : MachineData}, ∀ (h : checked W whole d = some d'),
    d' = d ∧ d.ok = true ∧ (⟨W, whole⟩ : Σ w : Nat, Term (.bits w)) = ⟨_, d.packed⟩

/-- Signature of `dataOfFrom`: the helper results are ARGUMENTS. -/
def expDataOfFrom (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape)
    (tin : Lean.Expr) (fl : Lean.Expr → Lean.Expr) : Option MachineData := none

/-- Signature of `dataOfAt`: no helper-result arguments. -/
def expDataOfAt (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape) :
    Option MachineData := none

/-! ## 2. Mutants (well-typed one-point changes; signature / defeq rejections) -/

def MutFromNoOk : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ok = false ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

def MutFromBposVpos : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.vpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

def MutFromBodyLen : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.nIn (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

def MutFromShapeBody : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (h : dataOfFrom lvl E senv s tin fl = some d),
    d.shape.body = s.body ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

def MutAtNoInit : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData},
    ∀ (h : dataOfAt lvl E senv s = some d),
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

def MutCheckedNoWidth : Prop :=
  ∀ {W : Nat} {whole : Term (.bits W)} {d d' : MachineData}, ∀ (h : checked W whole d = some d'),
    d' = d ∧ d.ok = true

/-- A different function signature: the helper results `tin` dropped (so a `partial` call would be inside). -/
def expDataOfFromNoTin (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape)
    (fl : Lean.Expr → Lean.Expr) : Option MachineData := none

/-- Signature check for `def`s (the Prop comparator does not apply): the two TYPES must be defeq. -/
def checkSig (c e : Name) : MetaM Unit := do
  let a := (← getConstInfo c).type
  let b := (← getConstInfo e).type
  unless (← isDefEq a b) do throwError "DATAOF3 SIGNATURE FAILED {c} against {e}"
  logInfo m!"DATAOF3 SIGNATURE OK {c} against {e}"

def checkSigMutant (c e : Name) : MetaM Unit := do
  let a := (← getConstInfo c).type
  let b := (← getConstInfo e).type
  if (← withoutModifyingState (isDefEq a b)) then throwError "DATAOF3 SIGNATURE MUTANT ACCEPTED {e} for {c}"
  logInfo m!"DATAOF3 SIGNATURE MUTANT REJECTED {e} (against {c}; type-level rejection, not a semantic counterexample)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``dataOfFrom_sound ``ExpDataOfFromSound
  checkExpected ``dataOfAt_sound ``ExpDataOfAtSound
  checkExpected ``dataOfCore_sound ``ExpDataOfCoreSound
  checkExpected ``checked_sound ``ExpCheckedSound
  checkSig ``dataOfFrom ``expDataOfFrom
  checkSig ``dataOfAt ``expDataOfAt
  checkMutant ``dataOfFrom_sound ``MutFromNoOk
  checkMutant ``dataOfFrom_sound ``MutFromBposVpos
  checkMutant ``dataOfFrom_sound ``MutFromBodyLen
  checkMutant ``dataOfFrom_sound ``MutFromShapeBody
  checkMutant ``dataOfAt_sound ``MutAtNoInit
  checkMutant ``checked_sound ``MutCheckedNoWidth
  checkSigMutant ``dataOfFrom ``expDataOfFromNoTin
  checkSigMutant ``dataOfFrom ``expDataOfAt

/-! ## 3. Kernel controls on the small total pieces -/

/-- `typedFields` does NOT check a `.bits n` width: width 16 against binder `.bits 8` is accepted (the width is `ok`'s job). -/
example : typedFields [.bits 8] [⟨16, .bitsLit 16 0⟩] = some [⟨.bits 16, .bitsLit 16 0⟩] := rfl
/-- A Bool binder takes the condition of a mux, a non-mux field is refused. -/
example : typedFields [.bool] [⟨1, .mux (.boolLit true) (.bitsLit 1 1) (.bitsLit 1 0)⟩] = some [⟨.bool, .boolLit true⟩] := rfl
example : typedFields [.bool] [⟨1, .bitsLit 1 1⟩] = none := rfl
/-- `zip` truncates: the lengths are fixed by the splits and the `ok` rows, not by `typedFields`. -/
example : typedFields [.bool] [] = some [] := rfl
/-- A domain placeholder that is a root `let` is refused; otherwise it is the placeholder. -/
example : srcDom'Of (.bvar 0) 1 = none := rfl
example : srcDom'Of (.bvar 3) 1 = some (machIn 2) := rfl
example : srcDom'Of (.const ``Nat []) 5 = some (.const ``Nat []) := rfl

/-! ## 4. Value closure (explicit walk) -/

open Tests.Gen5.DataOfCheck in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- the detector's own controls (same detector, same fixtures as DataOfCheck)
  unless badProj (.proj `Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "DATAOF3 AUDIT FAILED: raw T1Hyp proj missed"
  let F := `Tests.Gen5.DataOfFixture
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badNDCases, true), (F ++ `badEqual, true), (F ++ `unrelated, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "DATAOF3 AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "DATAOF3 AUDIT FAILED: detector flags {c}"
    logInfo m!"DATAOF3 CONTROL {c}: {toString r.hit}"
  for c in [``dataOfFrom_sound, ``dataOfAt_sound, ``dataOfCore_sound, ``checked_sound, ``dataOfTail_sound,
      ``dataOfFrom, ``dataOfAt] do
    let r ← reach c
    if let some p := r.hit then throwError "DATAOF3 AUDIT FAILED {c}: forbidden use via {p}"
    logInfo m!"DATAOF3 REACH {c}: no T1Hyp / T1HypND / Expr.equal / Expr.eqv / ofReduceBool; visited {r.visited}, body-less {r.noBody}, opaque {r.opaques} {r.opaqueNames} (an opaque or `partial` constant's body is NOT explored)"

/-! ## 5. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``dataOfFrom_sound, ``dataOfAt_sound, ``dataOfCore_sound, ``checked_sound, ``dataOfTail_sound] do
    checkAxioms n

end Tests.Gen5.DataOfCheck3
