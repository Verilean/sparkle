import Tools.ShippingGen5ReaderTraceApp
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: U-R4a checks, written against freeze rev5 `scripts/gen5/DG_READERTRACE_FREEZE_REV5.md` §4; clean issue-linked build pending (coder). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4a checks (Tools/ShippingGen5ReaderTraceApp.lean)

TYPE: the 4 theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceAppCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpExprPhSlot : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat}
    (hTr : TrInv senv nDecl st) (hi : i < st.kinds.size),
    FReachC nDecl st st ∧ ExprPh senv nDecl d (machSlot i, st)

abbrev ConcB (senv : StructEnv) (nDecl : Nat) (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead) : Prop :=
  TracePre senv nDecl (Call.conv env d (.app f a) st)

def ExpBareFound : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (hgate : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false)
    (e0 : Lean.Expr) (k : Nat)
    (hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) = some (e0, k))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

def ExpLoopRead : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (i : Nat) (hl : machLoopRead? env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

def ExpReadV : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (hics : machInstCallS? senv (.app f a) = none)
    (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (i : Nat) (hr : machReadV env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

-- theorem mutants (well-typed single changes)
def MutSlotNoHi : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat},
    TrInv senv nDecl st → FReachC nDecl st st ∧ ExprPh senv nDecl d (machSlot i, st)
def MutSlotNoReach : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat},
    TrInv senv nDecl st → i < st.kinds.size → ExprPh senv nDecl d (machSlot i, st)
def MutSlotLe : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat},
    TrInv senv nDecl st → i ≤ st.kinds.size → FReachC nDecl st st ∧ ExprPh senv nDecl d (machSlot i, st)
def MutSlotNextIdx : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat},
    TrInv senv nDecl st → i < st.kinds.size → FReachC nDecl st st ∧ ExprPh senv nDecl d (machSlot (i + 1), st)
def MutBareNoGate : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    ∀ (e0 : Lean.Expr) (k : Nat), st.bareRegs.find? (·.1 == Lean.Expr.app f a) = some (e0, k) →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutBareNoPhPost : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false →
    ∀ (e0 : Lean.Expr) (k : Nat), st.bareRegs.find? (·.1 == Lean.Expr.app f a) = some (e0, k) →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v)
def MutLoopReadRegSome : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (i : Nat) (hl : machLoopRead? env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutLoopReadNoPhPost : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none →
    ∀ (i : Nat), machLoopRead? env d (.app f a) = some i →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v)
def MutReadVNoMem : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none →
    machLoopRead? env d (.app f a) = none →
    machRunApp? (.app f a) = none →
    machInstCall? senv (.app f a) = none →
    machInstCallS? senv (.app f a) = none →
    ∀ (i : Nat), machReadV env d (.app f a) = some i →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutReadVLoopSome : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none →
    ∀ (i : Nat), machLoopRead? env d (.app f a) = some i →
    machRunApp? (.app f a) = none →
    machInstCall? senv (.app f a) = none →
    machInstCallS? senv (.app f a) = none →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none →
    machReadV env d (.app f a) = some i →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``exprPh_slot ``ExpExprPhSlot
  checkExpected ``conv_app_bareFound_trace ``ExpBareFound
  checkExpected ``conv_app_loopRead_trace ``ExpLoopRead
  checkExpected ``conv_app_readV_trace ``ExpReadV
  logInfo m!"GEN5 APPCHECK TYPE 4 theorems compared"
  checkMutant ``exprPh_slot ``MutSlotNoHi
  checkMutant ``exprPh_slot ``MutSlotNoReach
  checkMutant ``exprPh_slot ``MutSlotLe
  checkMutant ``exprPh_slot ``MutSlotNextIdx
  checkMutant ``conv_app_bareFound_trace ``MutBareNoGate
  checkMutant ``conv_app_bareFound_trace ``MutBareNoPhPost
  checkMutant ``conv_app_loopRead_trace ``MutLoopReadRegSome
  checkMutant ``conv_app_loopRead_trace ``MutLoopReadNoPhPost
  checkMutant ``conv_app_readV_trace ``MutReadVNoMem
  checkMutant ``conv_app_readV_trace ``MutReadVLoopSome
  logInfo m!"GEN5 APPCHECK MUTANT 10 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``exprPh_slot, ``conv_app_bareFound_trace, ``conv_app_loopRead_trace, ``conv_app_readV_trace]
def allThms : List Name := newThms

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n
  logInfo m!"GEN5 APPCHECK AXIOMS {allThms.length} theorems checked (standard axioms only)"

def closureRoots : List Name := allThms

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
    addDecl (.thmDecl { name := `ReaderTraceApp.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceApp.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceApp.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceApp.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceApp.direct, `ReaderTraceApp.viaHelper, `ReaderTraceApp.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 APPCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 APPCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceApp.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 APPCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 APPCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceApp.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceApp.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceApp.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceApp.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceApp.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceApp.Missing.nowhere do throwError "GEN5 APPCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceApp.viaHelperU, `ReaderTraceApp.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceApp.Missing.nowhere do throwError "GEN5 APPCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceApp.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 APPCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 APPCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 4 do throwError "GEN5 APPCHECK CLOSURE FAILED: expected 4 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 APPCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 APPCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 APPCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 APPCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 APPCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (4 theorems); all 4 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceAppCheck
