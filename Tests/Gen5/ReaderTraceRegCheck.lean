import Tools.ShippingGen5ReaderTraceReg
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: written against freeze rev6 `scripts/gen5/DG_READERTRACE_FREEZE_REV6.md` §1; build result and clean issue-linked build pending. No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4b checks (Tools/ShippingGen5ReaderTraceReg.lean)

TYPE: the 3 frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); the helpers `ph_argsAcc` / `trInv_pushReg` are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceRegCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpPhArgs : Prop := ∀ {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true),
    ∀ a ∈ e.getAppArgs, NoPh a = true ∧ BvarLt L a = true

def ExpRegViewPh : Prop := ∀ {L : Nat} {e dom α init x : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : regView? e.getAppFn e.getAppArgs = some (dom, α, init, x)),
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh x = true ∧ BvarLt L x = true)

def ExpBareNew : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (hgate : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false)
    (hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

-- theorem mutants (well-typed single changes)
def MutPhArgsNoBvar : Prop := ∀ {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true),
    ∀ a ∈ e.getAppArgs, NoPh a = true
def MutPhArgsNoPh : Prop := ∀ {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true),
    ∀ a ∈ e.getAppArgs, BvarLt L a = true
def MutPhArgsLPlus : Prop := ∀ {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true),
    ∀ a ∈ e.getAppArgs, NoPh a = true ∧ BvarLt (L + 1) a = true
def MutRegViewNoX : Prop := ∀ {L : Nat} {e dom α init x : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : regView? e.getAppFn e.getAppArgs = some (dom, α, init, x)),
    (NoPh dom = true ∧ BvarLt L dom = true)
def MutRegViewNoHb : Prop := ∀ {L : Nat} {e dom α init x : Lean.Expr} (hn : NoPh e = true)
    (h : regView? e.getAppFn e.getAppArgs = some (dom, α, init, x)),
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh x = true ∧ BvarLt L x = true)
def MutRegViewNone : Prop := ∀ {L : Nat} {e dom α init x : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : regView? e.getAppFn e.getAppArgs = none),
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh x = true ∧ BvarLt L x = true)
def MutBareNewNoGate : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutBareNewFindSome : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false →
    ∀ (e0 : Lean.Expr) (k : Nat), st.bareRegs.find? (·.1 == Lean.Expr.app f a) = some (e0, k) →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutBareNewNoPhPost : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false →
    st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v)
def MutBareNewNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false →
    st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
def MutBareNewNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead),
    TracePre senv nDecl (Call.conv env d (.app f a) st) →
    ∀ (dom α init x : Lean.Expr),
    regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x) →
    (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false →
    st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none →
    ∀ (v : (Call.conv env d (.app f a) st).Res),
    (convStep senv env d (.app f a) st).run (readF senv n) = some (some v) →
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``phArgs_getAppArgs ``ExpPhArgs
  checkExpected ``regView_ph ``ExpRegViewPh
  checkExpected ``conv_app_bareNew_trace ``ExpBareNew
  logInfo m!"GEN5 REGCHECK TYPE 3 theorems compared"
  checkMutant ``phArgs_getAppArgs ``MutPhArgsNoBvar
  checkMutant ``phArgs_getAppArgs ``MutPhArgsNoPh
  checkMutant ``phArgs_getAppArgs ``MutPhArgsLPlus
  checkMutant ``regView_ph ``MutRegViewNoX
  checkMutant ``regView_ph ``MutRegViewNoHb
  checkMutant ``regView_ph ``MutRegViewNone
  checkMutant ``conv_app_bareNew_trace ``MutBareNewNoGate
  checkMutant ``conv_app_bareNew_trace ``MutBareNewFindSome
  checkMutant ``conv_app_bareNew_trace ``MutBareNewNoPhPost
  checkMutant ``conv_app_bareNew_trace ``MutBareNewNoReach
  checkMutant ``conv_app_bareNew_trace ``MutBareNewNoHT
  logInfo m!"GEN5 REGCHECK MUTANT 11 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``ph_argsAcc, ``phArgs_getAppArgs, ``regView_ph, ``trInv_pushReg, ``conv_app_bareNew_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 REGCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceReg.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceReg.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceReg.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceReg.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceReg.direct, `ReaderTraceReg.viaHelper, `ReaderTraceReg.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 REGCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 REGCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceReg.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 REGCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 REGCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceReg.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceReg.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceReg.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceReg.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceReg.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceReg.Missing.nowhere do throwError "GEN5 REGCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceReg.viaHelperU, `ReaderTraceReg.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceReg.Missing.nowhere do throwError "GEN5 REGCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceReg.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 REGCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 REGCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 5 do throwError "GEN5 REGCHECK CLOSURE FAILED: expected 5 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 REGCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 REGCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 REGCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 REGCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 REGCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (5 theorems); all 5 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceRegCheck
