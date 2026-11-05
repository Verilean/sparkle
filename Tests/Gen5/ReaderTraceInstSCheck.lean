import Tools.ShippingGen5ReaderTraceInstS
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceInstSCheck, exit 0, 761 jobs; TYPE 2, MUTANT 4 signature/defeq rejections not semantic counterexamples, AXIOMS 7 standard only, CLOSURE OK 5022 constants from 7 roots; 3 intended in-memory sorry negatives print warnings) on the tree of this file's commit. No sorry / axiom / native_decide in source.
/-! # DG-READERTRACE U-R8 checks (Tools/ShippingGen5ReaderTraceInstS.lean)

TYPE: `instRes_ph` and `instS_trace` are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling; rev12 §1 / §4); the other new declarations are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). `InstSFieldsDet` is a named hypothesis, not claimed true.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceInstSCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType Tools.Assume.EnvInstS
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpRes : Prop := ∀ (hI : Inst1Ph) {L : Nat} (args : List Lean.Expr) (ty r : Lean.Expr),
    NoPh ty = true → BvarLt L ty = true → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
    instRes ty args = some r → NoPh r = true ∧ BvarLt L r = true
def ExpInstS : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hI : Inst1Ph) (hD : InstSFieldsDet senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.instS env c kinds ty args st))
    (r : (Call.instS env c kinds ty args st).Res)
    (hv : (instSStep senv env c kinds ty args st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.instS env c kinds ty args st) r) ∧
    PhPost senv nDecl (Call.instS env c kinds ty args st) r

def MutNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hI : Inst1Ph) (hD : InstSFieldsDet senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.instS env c kinds ty args st))
    (r : (Call.instS env c kinds ty args st).Res)
    (hv : (instSStep senv env c kinds ty args st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.instS env c kinds ty args st) r
def MutNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hI : Inst1Ph) (hD : InstSFieldsDet senv)
    (env : List MachVal) (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.instS env c kinds ty args st))
    (r : (Call.instS env c kinds ty args st).Res)
    (hv : (instSStep senv env c kinds ty args st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.instS env c kinds ty args st) r) ∧
    PhPost senv nDecl (Call.instS env c kinds ty args st) r
def MutNoInst1 : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hD : InstSFieldsDet senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.instS env c kinds ty args st))
    (r : (Call.instS env c kinds ty args st).Res)
    (hv : (instSStep senv env c kinds ty args st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.instS env c kinds ty args st) r) ∧
    PhPost senv nDecl (Call.instS env c kinds ty args st) r
def MutResNoBvar : Prop := ∀ (hI : Inst1Ph) {L : Nat} (args : List Lean.Expr) (ty r : Lean.Expr),
    NoPh ty = true → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
    instRes ty args = some r → NoPh r = true ∧ BvarLt L r = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``instRes_ph ``ExpRes
  checkExpected ``instS_trace ``ExpInstS
  logInfo m!"GEN5 INSTSCHECK TYPE 2 theorems compared"
  checkMutant ``instS_trace ``MutNoReach
  checkMutant ``instS_trace ``MutNoHT
  checkMutant ``instS_trace ``MutNoInst1
  checkMutant ``instRes_ph ``MutResNoBvar
  logInfo m!"GEN5 INSTSCHECK MUTANT 4 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``instRes_ph, ``inRange_foldApp, ``instS_expr, ``trInv_pushGroup, ``instSArg_trace,
  ``instSParam_trace, ``instS_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 INSTSCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceInstSCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceInstSCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceInstSCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceInstSCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceInstSCheck.direct, `ReaderTraceInstSCheck.viaHelper, `ReaderTraceInstSCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 INSTSCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 INSTSCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceInstSCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 INSTSCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 INSTSCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceInstSCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInstSCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInstSCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceInstSCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceInstSCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceInstSCheck.Missing.nowhere do throwError "GEN5 INSTSCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceInstSCheck.viaHelperU, `ReaderTraceInstSCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceInstSCheck.Missing.nowhere do throwError "GEN5 INSTSCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceInstSCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 INSTSCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 INSTSCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 7 do throwError "GEN5 INSTSCHECK CLOSURE FAILED: expected 7 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 INSTSCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 INSTSCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 INSTSCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 INSTSCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 INSTSCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (7 theorems); all 7 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceInstSCheck
