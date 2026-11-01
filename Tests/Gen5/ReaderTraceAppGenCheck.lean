import Tools.ShippingGen5ReaderTraceAppGen
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: written against freeze `scripts/gen5/DG_READERTRACE_FREEZE_REV7.md` §3; build result and clean issue-linked build pending. No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4d checks (Tools/ShippingGen5ReaderTraceAppGen.lean)

TYPE: the frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); helpers are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceAppGenCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv 

section Expected
def ExpAppGeneral : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

-- theorem mutants (well-typed single changes)
def MutAppGenNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutAppGenNoHr : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutAppGenNoHmem : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutAppGenNoHl : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutAppGenRegSome : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (dom α init x : Lean.Expr) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x)) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutAppGenReadVSome : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (i : Nat) (hr : machReadV env d (.app f a) = some i) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutAppGenNoPhPost : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v)
def MutAppGenNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st)) (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none) (hl : machLoopRead? env d (.app f a) = none) (hrun : machRunApp? (.app f a) = none) (hic : machInstCall? senv (.app f a) = none) (hics : machInstCallS? senv (.app f a) = none) (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none) (hr : machReadV env d (.app f a) = none) (v : (Call.conv env d (.app f a) st).Res) (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``conv_app_general_trace ``ExpAppGeneral
  logInfo m!"GEN5 APPGENCHECK TYPE 1 theorems compared"
  checkMutant ``conv_app_general_trace ``MutAppGenNoHT
  checkMutant ``conv_app_general_trace ``MutAppGenNoHr
  checkMutant ``conv_app_general_trace ``MutAppGenNoHmem
  checkMutant ``conv_app_general_trace ``MutAppGenNoHl
  checkMutant ``conv_app_general_trace ``MutAppGenRegSome
  checkMutant ``conv_app_general_trace ``MutAppGenReadVSome
  checkMutant ``conv_app_general_trace ``MutAppGenNoPhPost
  checkMutant ``conv_app_general_trace ``MutAppGenNoReach
  logInfo m!"GEN5 APPGENCHECK MUTANT 8 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``conv_app_general_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 APPGENCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceAppGenCheck.direct, `ReaderTraceAppGenCheck.viaHelper, `ReaderTraceAppGenCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 APPGENCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 APPGENCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceAppGenCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 APPGENCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 APPGENCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceAppGenCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceAppGenCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceAppGenCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceAppGenCheck.Missing.nowhere do throwError "GEN5 APPGENCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceAppGenCheck.viaHelperU, `ReaderTraceAppGenCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceAppGenCheck.Missing.nowhere do throwError "GEN5 APPGENCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceAppGenCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 APPGENCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 APPGENCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 1 do throwError "GEN5 APPGENCHECK CLOSURE FAILED: expected 1 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 APPGENCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 APPGENCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 APPGENCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 APPGENCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 APPGENCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (1 theorems); all 1 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceAppGenCheck
