import Tools.ShippingGen5ReaderTraceSigTy
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: written against freeze rev9 `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §3 (U-R4e2). No sorry / axiom / native_decide in source; the closure-control negatives are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4e2 checks (Tools/ShippingGen5ReaderTraceSigTy.lean)

TYPE: `sigTyPh_of` and `machInstCallS?_ty_ph` are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); `noPh_of_noFv` is checked by AXIOMS and CLOSURE only.
The closure also contains the named condition `SigTyClosed` (a `Prop` def, not an axiom). Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceSigTyCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Assume.EnvSigTy

section Expected

def ExpSigTyPh : Prop := ∀ (env : Lean.Environment) (hK : EnvTypesFVarFree env) (hC : SigTyClosed (structEnv env)),
    SigTyPh (structEnv env)
def ExpTyPh : Prop := ∀ {senv : StructEnv} (hS : SigTyPh senv)
    {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (h : machInstCallS? senv e = some (c, kinds, ty, args)), NoPh ty = true ∧ BvarLt 0 ty = true

def MutSigTyPhNoC : Prop := ∀ (env : Lean.Environment), EnvTypesFVarFree env →
    ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
      (structEnv env).instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true
def MutSigTyPhNoK : Prop := ∀ (env : Lean.Environment), SigTyClosed (structEnv env) →
    ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
      (structEnv env).instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true
def MutSigTyPhL1 : Prop := ∀ (env : Lean.Environment), EnvTypesFVarFree env → SigTyClosed (structEnv env) →
    ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
      (structEnv env).instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 1 ty = true
def MutTyPhNoPhOnly : Prop := ∀ {senv : StructEnv}, (∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
      senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true) →
    ∀ {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr},
      machInstCallS? senv e = some (c, kinds, ty, args) → NoPh ty = true
def MutTyPhL1 : Prop := ∀ {senv : StructEnv}, (∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
      senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true) →
    ∀ {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr},
      machInstCallS? senv e = some (c, kinds, ty, args) → NoPh ty = true ∧ BvarLt 1 ty = true
def MutTyPhNoHS : Prop := ∀ {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr},
      machInstCallS? senv e = some (c, kinds, ty, args) → NoPh ty = true ∧ BvarLt 0 ty = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``sigTyPh_of ``ExpSigTyPh
  checkExpected ``machInstCallS?_ty_ph ``ExpTyPh
  logInfo m!"GEN5 SIGTYCHECK TYPE 2 theorems compared"
  checkMutant ``sigTyPh_of ``MutSigTyPhNoC
  checkMutant ``sigTyPh_of ``MutSigTyPhNoK
  checkMutant ``sigTyPh_of ``MutSigTyPhL1
  checkMutant ``machInstCallS?_ty_ph ``MutTyPhNoPhOnly
  checkMutant ``machInstCallS?_ty_ph ``MutTyPhL1
  checkMutant ``machInstCallS?_ty_ph ``MutTyPhNoHS
  logInfo m!"GEN5 SIGTYCHECK MUTANT 6 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``noPh_of_noFv, ``sigTyPh_of, ``machInstCallS?_ty_ph]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 SIGTYCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

def closureRoots : List Name := newThms

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file): each must be detected; clean controls must not be.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceSigTyCheck.direct, `ReaderTraceSigTyCheck.viaHelper, `ReaderTraceSigTyCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 SIGTYCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 SIGTYCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceSigTyCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 SIGTYCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 SIGTYCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceSigTyCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceSigTyCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceSigTyCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceSigTyCheck.Missing.nowhere do throwError "GEN5 SIGTYCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceSigTyCheck.viaHelperU, `ReaderTraceSigTyCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceSigTyCheck.Missing.nowhere do throwError "GEN5 SIGTYCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceSigTyCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 SIGTYCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 SIGTYCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 3 do throwError "GEN5 SIGTYCHECK CLOSURE FAILED: expected 3 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 SIGTYCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 SIGTYCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 SIGTYCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 SIGTYCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 SIGTYCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (3 theorems); all 3 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceSigTyCheck
