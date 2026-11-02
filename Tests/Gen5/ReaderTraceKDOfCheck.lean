import Tools.ShippingGen5ReaderTraceKDOf
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (header updated with the built SHA after the Pod build). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # RT C.CV-3 checks (`Tools/ShippingGen5ReaderTraceKDOf.lean`)

TYPE: the 2 theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). -/

namespace Tests.Gen5.ReaderTraceKDOfCheck
open Lean Meta Elab Sparkle.Compiler.Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Sem Tools.ShippingGen5DataOf Tools.ShippingMachineAuto
  Tests.Gen3.ExpectedType

section Expected

def ExpFrom : Prop := ∀ (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h :
    dataOfFrom lvl (Lean.ConstantInfo.defnInfo dv) senv s
      (Sparkle.Compiler.MachTupleIn.packTupleInputs dv.value) fl = some d),
    kDOf d = nDeclOfCi (Lean.ConstantInfo.defnInfo dv)
def ExpAt : Prop := ∀ (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {d : MachineData}
    (h :
    dataOfAt lvl (Lean.ConstantInfo.defnInfo dv) senv s = some d),
    kDOf d = nDeclOfCi (Lean.ConstantInfo.defnInfo dv)
def MutFromLe : Prop := ∀ (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h :
    dataOfFrom lvl (Lean.ConstantInfo.defnInfo dv) senv s
      (Sparkle.Compiler.MachTupleIn.packTupleInputs dv.value) fl = some d),
    kDOf d ≤ nDeclOfCi (Lean.ConstantInfo.defnInfo dv)
def MutAtNIn : Prop := ∀ (lvl : Lean.Expr → Nat) {dv : Lean.DefinitionVal} {senv : StructEnv}
    {s : MachineShape} {d : MachineData}
    (h :
    dataOfAt lvl (Lean.ConstantInfo.defnInfo dv) senv s = some d),
    d.nIn = nDeclOfCi (Lean.ConstantInfo.defnInfo dv)

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``kDOf_eq_nDeclOfCi_of_dataOfFrom ``ExpFrom
  checkExpected ``kDOf_eq_nDeclOfCi ``ExpAt
  logInfo m!"GEN5 KDOFCHECK TYPE 2 declarations compared"
  checkMutant ``kDOf_eq_nDeclOfCi_of_dataOfFrom ``MutFromLe
  checkMutant ``kDOf_eq_nDeclOfCi ``MutAtNIn
  logInfo m!"GEN5 KDOFCHECK MUTANT 2 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"
  logInfo m!"GEN5 KDOFCHECK COUNTS: TYPE 2 / MUTANT 2"

def newThms : List Name := [``kDOf_eq_nDeclOfCi_of_dataOfFrom, ``kDOf_eq_nDeclOfCi]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 KDOFCHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match ci with
    | .thmInfo v => for c in v.value.getUsedConstants do closureOf env c
    | .defnInfo v => for c in v.value.getUsedConstants do closureOf env c
    | .opaqueInfo v => for c in v.value.getUsedConstants do closureOf env c
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (_, (seen, unk)) ← (newThms.forM (closureOf env)).run ({}, {})
  for n in newThms do
    unless seen.contains n do throwError "GEN5 KDOFCHECK CLOSURE FAILED: {n} not in seen set"
  let hits := forbiddenConsts.filter seen.contains
  unless hits.isEmpty do throwError "GEN5 KDOFCHECK CLOSURE FAILED: forbidden constants {hits}"
  unless unk.isEmpty do throwError "GEN5 KDOFCHECK CLOSURE FAILED: unknown constants {unk.toList}"
  logInfo m!"GEN5 KDOFCHECK CLOSURE OK: {seen.toList.length} constants from {newThms.length} roots; no sorryAx / ofReduceBool / trustCompiler"

end Tests.Gen5.ReaderTraceKDOfCheck
