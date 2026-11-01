import Tools.ShippingGen5SemDataOfParts
import Tests.Gen5.GenDataCheck
set_option autoImplicit false
-- NOT BUILT HERE (U9 check, scripts/gen5/DG_SEM_FREEZE_P9.md §2.2). Pod incremental build exit 0 (721 jobs) at Lean tree 766e78a2: TYPE OK 2 (no defeq-only), MUTANT REJECTED 11 (of_parts 6, parts 5), AXIOMS OK 2 standard, CLOSURE OK + controls; clean build is the coder's. Mutants are rejected by signature comparison, not semantic counterexamples. No sorry/axiom/native_decide.
/-! # DG-SEM U9 check (Tools/ShippingGen5SemDataOfParts.lean): 2 theorems typed against independent `Exp*`; no new def/structure (U8's `DataOfSound` value stays covered by `GenDataCheck`). Not connected to the real `dataOfAt_sound`. -/
namespace Tests.Gen5.SemDataOfPartsCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingMachineSource Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge

def ExpDataOfSoundOfParts : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = true),
    DataOfSound dataOf initsOf

def ExpDataOfSoundParts : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true)

def MutOPNoInit : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed),
    DataOfSound dataOf initsOf

def MutOPInitFalse : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = false),
    DataOfSound dataOf initsOf

def MutOPInitConverse : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.initOk (initsOf d) = true → d.ok = true),
    DataOfSound dataOf initsOf

def MutOPHfOkFalse : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = false ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = true),
    DataOfSound dataOf initsOf

def MutOPHfNoShape : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = true),
    DataOfSound dataOf initsOf

def MutOPHfReorder : Prop := ∀ (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss))
    (hf : ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.ok = true ∧ d.shape = s ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : ∀ d : MachineData, d.ok = true → d.initOk (initsOf d) = true),
    DataOfSound dataOf initsOf

def MutPInitFalse : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = false)

def MutPReorder : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.ok = true ∧ d.shape = s ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true)

def MutPSwapParts : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)

def MutPNoBody : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = true) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true)

def MutPOkFalse : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d →
      d.shape = s ∧ d.ok = false ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) ∧
    (∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
      dataOf E senv s = some d → d.initOk (initsOf d) = true)

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``dataOfSound_of_parts ``ExpDataOfSoundOfParts
  checkExpected ``dataOfSound_parts ``ExpDataOfSoundParts
  logInfo m!"GEN5 DATAOFPARTS TYPE OK 2 theorems against ExpDataOfSoundOfParts, ExpDataOfSoundParts"

run_cmd Lean.Elab.Command.liftTermElabM do
  let tm : List (Name × Name) :=
    [(``dataOfSound_of_parts, ``MutOPNoInit),
     (``dataOfSound_of_parts, ``MutOPInitFalse),
     (``dataOfSound_of_parts, ``MutOPInitConverse),
     (``dataOfSound_of_parts, ``MutOPHfOkFalse),
     (``dataOfSound_of_parts, ``MutOPHfNoShape),
     (``dataOfSound_of_parts, ``MutOPHfReorder),
     (``dataOfSound_parts, ``MutPInitFalse),
     (``dataOfSound_parts, ``MutPReorder),
     (``dataOfSound_parts, ``MutPSwapParts),
     (``dataOfSound_parts, ``MutPNoBody),
     (``dataOfSound_parts, ``MutPOkFalse)]
  for (t, m) in tm do checkMutant t m
  logInfo m!"GEN5 DATAOFPARTS COUNTS: TYPE 2 theorems; MUTANT {tm.length} total (of_parts 6, parts 5), each one well-typed change rejected by signature/defeq comparison, NOT a semantic counterexample; includes conjunct-order changes (MutOPHfReorder, MutPReorder, MutPSwapParts) and projection-affecting changes (MutPNoBody, MutPOkFalse)."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``dataOfSound_of_parts, ``dataOfSound_parts]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 DATAOFPARTS AXIOMS OK: {ns.length} roots, standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``dataOfSound_of_parts, ``dataOfSound_parts]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 DATAOFPARTS CLOSURE FAILED: forbidden constants {f}"
  unless c.seen.contains ``dataOfSound_of_parts do throwError "GEN5 DATAOFPARTS CONTROL FAILED: root itself not judged"
  unless c.seen.contains ``Tools.ShippingGen5Sem.DataOfSound do throwError "GEN5 DATAOFPARTS CONTROL FAILED: DataOfSound not reached"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemDataOfPartsCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 DATAOFPARTS CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 DATAOFPARTS CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 DATAOFPARTS CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 DATAOFPARTS CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 DATAOFPARTS CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 DATAOFPARTS CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 DATAOFPARTS CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 DATAOFPARTS CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 DATAOFPARTS CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: root judged, DataOfSound reached, unknown root throws, 2 forbidden roots flagged, unknown helper VALUE/TYPE flagged, clean fixture passes"

#print axioms dataOfSound_of_parts
#print axioms dataOfSound_parts

end Tests.Gen5.SemDataOfPartsCheck
