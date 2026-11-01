import Tools.ShippingGen5ReaderTraceDispatch
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceDispatchCheck, exit 0, 771 jobs; TYPE 3, MUTANT 4 signature/defeq rejections not semantic counterexamples, AXIOMS 11 standard only, CLOSURE OK 9127 constants from 11 roots, no sorryAx; 3 intended in-memory sorry negatives print warnings) on the tree of this file's commit. No sorry / axiom / native_decide in source.
/-! # DG-READERTRACE U-R11 checks (Tools/ShippingGen5ReaderTraceAppCall.lean, Tools/ShippingGen5ReaderTraceDispatch.lean)

TYPE: `readF_traceGood`, `readF_traceGood_of_premises`, `step_trace` are compared by `checkExpected` against `Exp…` statements written here (own spelling); the other new declarations are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). Every hypothesis (`LiftAgrees`, `RootFloatAgrees`, `Inst1Agrees`, `EnvTypesFVarFree`, `SigTyClosed`, `InstSFieldsDet`) is a named hypothesis, not claimed true.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceDispatchCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType Tools.Assume.EnvInstS
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
open Tools.ShippingLetsAliasInv

section Expected

def ExpReadF : Prop := ∀ (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat) (hla : LiftAgrees)
    (hrf : RootFloatAgrees) (hI : Inst1Ph) (hD : InstSFieldsDet senv) (hS : SigTyPh senv),
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)
def ExpPrem : Prop := ∀ (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hi1 : Inst1Agrees) (hD : InstSFieldsDet (structEnv env)) (nDecl : Nat),
    ∀ n : Nat, TraceGood (structEnv env) nDecl (readF (structEnv env) n)
def ExpStep : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees) (hI : Inst1Ph)
    (hD : InstSFieldsDet senv) (hS : SigTyPh senv) (n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (c : Call) (hpre : TracePre senv nDecl c) (v : c.Res)
    (hv : (step senv c).run (readF senv n) = some (some v)),
    FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v

def MutNoD : Prop := ∀ (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat) (hla : LiftAgrees)
    (hrf : RootFloatAgrees) (hI : Inst1Ph) (hS : SigTyPh senv),
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)
def MutNoLift : Prop := ∀ (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat)
    (hrf : RootFloatAgrees) (hI : Inst1Ph) (hD : InstSFieldsDet senv) (hS : SigTyPh senv),
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)
def MutPremNoClosed : Prop := ∀ (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hi1 : Inst1Agrees) (hD : InstSFieldsDet (structEnv env)) (nDecl : Nat),
    ∀ n : Nat, TraceGood (structEnv env) nDecl (readF (structEnv env) n)
def MutStepNoReach : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees) (hI : Inst1Ph)
    (hD : InstSFieldsDet senv) (hS : SigTyPh senv) (n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (c : Call) (hpre : TracePre senv nDecl c) (v : c.Res)
    (hv : (step senv c).run (readF senv n) = some (some v)),
    PhPost senv nDecl c v

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readF_traceGood ``ExpReadF
  checkExpected ``readF_traceGood_of_premises ``ExpPrem
  checkExpected ``step_trace ``ExpStep
  logInfo m!"GEN5 DISPATCHCHECK TYPE 3 theorems compared"
  checkMutant ``readF_traceGood ``MutNoD
  checkMutant ``readF_traceGood ``MutNoLift
  checkMutant ``readF_traceGood_of_premises ``MutPremNoClosed
  checkMutant ``step_trace ``MutStepNoReach
  logInfo m!"GEN5 DISPATCHCHECK MUTANT 4 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``memCall?_len, ``conv_app_nested_trace, ``conv_app_inst_trace, ``conv_app_instS_trace,
  ``conv_app_mem_trace, ``conv_app_trace, ``conv_trace, ``chain_trace, ``step_trace, ``readF_traceGood,
  ``readF_traceGood_of_premises]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 DISPATCHCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceDispatchCheck.direct, `ReaderTraceDispatchCheck.viaHelper, `ReaderTraceDispatchCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 DISPATCHCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 DISPATCHCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceDispatchCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 DISPATCHCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 DISPATCHCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceDispatchCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceDispatchCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceDispatchCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceDispatchCheck.Missing.nowhere do throwError "GEN5 DISPATCHCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceDispatchCheck.viaHelperU, `ReaderTraceDispatchCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceDispatchCheck.Missing.nowhere do throwError "GEN5 DISPATCHCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceDispatchCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 DISPATCHCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 DISPATCHCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 11 do throwError "GEN5 DISPATCHCHECK CLOSURE FAILED: expected 11 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 DISPATCHCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 DISPATCHCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 DISPATCHCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 DISPATCHCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 DISPATCHCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (11 theorems); all 11 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceDispatchCheck
