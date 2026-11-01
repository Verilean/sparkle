import Tools.ShippingGen5ReaderTraceLoopRoot
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT YET. Written against freeze rev13 `scripts/gen5/DG_READERTRACE_FREEZE_REV13.md` (U-R9 / U-R10). No sorry / axiom / native_decide in source; the closure-control negatives are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R9 / U-R10 checks (Tools/ShippingGen5ReaderTraceLoop.lean, Tools/ShippingGen5ReaderTraceLoopRoot.lean)

TYPE: `loopBody_trace`, `loopFold_trace`, `loopProbe_trace`, `loopRoot_trace` are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); the other new declarations are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceLoopCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpFold : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (base : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (n0 : Nat) (hbase : base + n0 ≤ st0.kinds.size)
    (l : List (Lean.Expr × Lean.Expr × Lean.Expr)),
    (∀ a ∈ l, NoPh a.2.2 = true ∧ BvarLt (env.length + nDecl) a.2.2 = true) →
    ∀ (ws : List (Nat × Lean.Expr)) (st : MachRead), ws.length + l.length ≤ n0 →
      LoopFold senv nDecl st0 (ws, st) →
      SatP (readF senv n) (fun p : List (Nat × Lean.Expr) × MachRead => LoopFold senv nDecl st0 p ∧
          p.1.length = ws.length + l.length)
        (foldO (loopNext env base) (ws, st) l)
def ExpBody : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopBody base env e st))
    (r : (Call.loopBody base env e st).Res)
    (hv : (loopBodyStep base env e st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.loopBody base env e st) r) ∧
    PhPost senv nDecl (Call.loopBody base env e st) r
def ExpProbe : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (body : Lean.Expr) (m : Nat) (hnb : NoPh body = true)
    (hbb : BvarLt (env.length + 1 + nDecl) body = true)
    (hreglen : ∀ regs, machLoopRegs (machLetTail body) = some regs → regs.length = m)
    (s1 : MachRead) (hst : RdOk s1) (hE : EnvOk s1.lets.size env) (hTr : TrInv senv nDecl s1)
    (hEp : EnvPh nDecl s1 env),
    ∀ a, a ∈ s1.loopWs.toList →
      SatP (readF senv n) (fun p : Nat × MachRead => FReachC nDecl s1 p.2 ∧ TrInv senv nDecl p.2 ∧
          p.1 + m ≤ p.2.kinds.size) (loopProbe env body m s1 a)
def ExpRoot : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopRoot env e st))
    (r : (Call.loopRoot env e st).Res)
    (hv : (loopRootStep senv env e st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.loopRoot env e st) r) ∧
    PhPost senv nDecl (Call.loopRoot env e st) r

def MutBodyNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopBody base env e st))
    (r : (Call.loopBody base env e st).Res)
    (hv : (loopBodyStep base env e st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.loopBody base env e st) r
def MutBodyNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopBody base env e st))
    (r : (Call.loopBody base env e st).Res)
    (hv : (loopBodyStep base env e st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.loopBody base env e st) r) ∧
    PhPost senv nDecl (Call.loopBody base env e st) r
def MutRootNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopRoot env e st))
    (r : (Call.loopRoot env e st).Res)
    (hv : (loopRootStep senv env e st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.loopRoot env e st) r
def MutRootNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopRoot env e st))
    (r : (Call.loopRoot env e st).Res)
    (hv : (loopRootStep senv env e st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.loopRoot env e st) r) ∧
    PhPost senv nDecl (Call.loopRoot env e st) r
def MutFoldNoBound : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (base : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (n0 : Nat)
    (l : List (Lean.Expr × Lean.Expr × Lean.Expr)),
    (∀ a ∈ l, NoPh a.2.2 = true ∧ BvarLt (env.length + nDecl) a.2.2 = true) →
    ∀ (ws : List (Nat × Lean.Expr)) (st : MachRead), ws.length + l.length ≤ n0 →
      LoopFold senv nDecl st0 (ws, st) →
      SatP (readF senv n) (fun p : List (Nat × Lean.Expr) × MachRead => LoopFold senv nDecl st0 p ∧
          p.1.length = ws.length + l.length)
        (foldO (loopNext env base) (ws, st) l)
def MutProbeNoKinds : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (body : Lean.Expr) (m : Nat) (hnb : NoPh body = true)
    (hbb : BvarLt (env.length + 1 + nDecl) body = true)
    (hreglen : ∀ regs, machLoopRegs (machLetTail body) = some regs → regs.length = m)
    (s1 : MachRead) (hst : RdOk s1) (hE : EnvOk s1.lets.size env) (hTr : TrInv senv nDecl s1)
    (hEp : EnvPh nDecl s1 env),
    ∀ a, a ∈ s1.loopWs.toList →
      SatP (readF senv n) (fun p : Nat × MachRead => FReachC nDecl s1 p.2 ∧ TrInv senv nDecl p.2)
        (loopProbe env body m s1 a)

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``loopFold_trace ``ExpFold
  checkExpected ``loopBody_trace ``ExpBody
  checkExpected ``loopProbe_trace ``ExpProbe
  checkExpected ``loopRoot_trace ``ExpRoot
  logInfo m!"GEN5 LOOPCHECK TYPE 4 theorems compared"
  checkMutant ``loopBody_trace ``MutBodyNoReach
  checkMutant ``loopBody_trace ``MutBodyNoHT
  checkMutant ``loopRoot_trace ``MutRootNoReach
  checkMutant ``loopRoot_trace ``MutRootNoHT
  checkMutant ``loopFold_trace ``MutFoldNoBound
  checkMutant ``loopProbe_trace ``MutProbeNoKinds
  logInfo m!"GEN5 LOOPCHECK MUTANT 6 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``loopReg_ph, ``loopRegs_ph, ``resolve_ph, ``trInv_bindLetNamed, ``bindLetAlias_trace,
  ``loopLet_ph, ``loopNext_trace, ``loopFold_trace, ``loopBody_trace, ``inlSpine_ph, ``loopView_ph, ``mapM_len_some,
  ``trInv_pushLoop, ``envPh_cons_state, ``trInv_loopWs, ``loopProbe_trace, ``loopRoot_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 LOOPCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceLoopCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceLoopCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceLoopCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceLoopCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceLoopCheck.direct, `ReaderTraceLoopCheck.viaHelper, `ReaderTraceLoopCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 LOOPCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 LOOPCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceLoopCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 LOOPCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 LOOPCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceLoopCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceLoopCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceLoopCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceLoopCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceLoopCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceLoopCheck.Missing.nowhere do throwError "GEN5 LOOPCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceLoopCheck.viaHelperU, `ReaderTraceLoopCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceLoopCheck.Missing.nowhere do throwError "GEN5 LOOPCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceLoopCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 LOOPCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 LOOPCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 17 do throwError "GEN5 LOOPCHECK CLOSURE FAILED: expected 17 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 LOOPCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 LOOPCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 LOOPCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 LOOPCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 LOOPCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (17 theorems); all 17 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceLoopCheck
