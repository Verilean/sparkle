import Tools.ShippingGen5ReaderTraceChainLet
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceChainLetCheck, exit 0; TYPE 1 theorem; MUTANT 3 theorem-statement mutants (signature/defeq rejections, not semantic counterexamples); AXIOMS 1 (standard only); CLOSURE OK 4925 constants from 1 root, 1 target seen; 3 intended in-memory sorry negatives print warnings) on the tree of 745e7fda39e8aa60e718ae54ce43c87ee4cfdae0 (Lean content identical; this header is comment-only). Written against freeze rev10 addendum §2 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R5b). No sorry / axiom / native_decide in source; the closure-control negatives are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R5b checks (Tools/ShippingGen5ReaderTraceChainLet.lean)

TYPE: `chain_letE_trace` is compared by `checkExpected` against an `Exp…` statement written here from the freeze text (own spelling).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
CLOSURE: value-closure walk from the new declaration, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceChainLetCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpChainLetE : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.chain env (.letE nm ty v b nd) st))
    (r : (Call.chain env (.letE nm ty v b nd) st).Res)
    (hv : (chainStep senv env (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.chain env (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.chain env (.letE nm ty v b nd) st) r

def MutChainLetENoHla : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.chain env (.letE nm ty v b nd) st))
    (r : (Call.chain env (.letE nm ty v b nd) st).Res)
    (hv : (chainStep senv env (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.chain env (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.chain env (.letE nm ty v b nd) st) r
def MutChainLetENoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.chain env (.letE nm ty v b nd) st))
    (r : (Call.chain env (.letE nm ty v b nd) st).Res)
    (hv : (chainStep senv env (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.chain env (.letE nm ty v b nd) st) r
def MutChainLetENoHpre : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (r : (Call.chain env (.letE nm ty v b nd) st).Res)
    (hv : (chainStep senv env (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.chain env (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.chain env (.letE nm ty v b nd) st) r

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``chain_letE_trace ``ExpChainLetE
  logInfo m!"GEN5 CHAINLETCHECK TYPE 1 theorems compared"
  checkMutant ``chain_letE_trace ``MutChainLetENoHla
  checkMutant ``chain_letE_trace ``MutChainLetENoReach
  checkMutant ``chain_letE_trace ``MutChainLetENoHpre
  logInfo m!"GEN5 CHAINLETCHECK MUTANT 3 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``chain_letE_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 CHAINLETCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceChainLetCheck.direct, `ReaderTraceChainLetCheck.viaHelper, `ReaderTraceChainLetCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 CHAINLETCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 CHAINLETCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceChainLetCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 CHAINLETCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 CHAINLETCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceChainLetCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceChainLetCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceChainLetCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceChainLetCheck.Missing.nowhere do throwError "GEN5 CHAINLETCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceChainLetCheck.viaHelperU, `ReaderTraceChainLetCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceChainLetCheck.Missing.nowhere do throwError "GEN5 CHAINLETCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceChainLetCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 CHAINLETCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 CHAINLETCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 1 do throwError "GEN5 CHAINLETCHECK CLOSURE FAILED: expected 1 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 CHAINLETCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 CHAINLETCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 CHAINLETCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 CHAINLETCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 CHAINLETCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (1 theorems); all 1 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceChainLetCheck
