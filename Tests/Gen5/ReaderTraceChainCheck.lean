import Tools.ShippingGen5ReaderTraceChain
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceChainCheck, exit 0) on the tree of a2005315 (this header is comment-only). Measured: TYPE 2 theorems + 1 match def (ChainBasic x 12 ctors) agree with independent versions + 1 agreement theorem; MUTANT 6 theorem-statement + 2 well-typed match-def mutants (rejected at exactly the changed ctor) = 8, no ill-typed variant counted; AXIOMS 3 theorems (propext / Classical.choice / Quot.sound only); CLOSURE OK 4655 constants from 4 roots, all 3 target declarations in seen, 3 negative + 3 forbidden-root self-hit + 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 warnings. Mutants are signature/defeq rejections, not semantic counterexamples. Clean issue-linked build: rt10v-04b00b00 exit 0 (726 jobs, dirty=false) at 04b00b00c797a6fad7af564f46cc5768d6d2322f. Written against freeze rev4 (approved at bc6b1e12). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R3b checks (Tools/ShippingGen5ReaderTraceChain.lean)

TYPE: `ChainBasic`, `envPh_cons_unit`, `chain_basic_trace` are compared by `checkExpected` (`Tests/Gen3/ExpectedType.lean`) against `Exp…` statements written here from the freeze text (own spelling).
Match def `ChainBasic`: independent `Exp` match version + a FULL-argument agreement theorem, plus the per-constructor comparer `exprAgree` (the SAME comparer for the real def and the mutants).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
`chain_basic_trace` is stated under `hT : TraceGood senv nDecl (readF senv n)` and `hv` (a successful run): both conditions are explicit in the statement compared here.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceChainCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpChainBasic : Lean.Expr → Prop
  | .letE _ _ _ _ _ => False
  | .bvar _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .app _ _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .lit _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True

theorem chainBasic_eq_exp : ∀ e : Lean.Expr, ChainBasic e ↔ ExpChainBasic e := by intro e; cases e <;> exact Iff.rfl

def ExpEnvPhConsUnit : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal}
    (h : EnvPh nDecl st env), EnvPh nDecl st (MachVal.unit :: env)

def ExpChainBasicTrace : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hb : ChainBasic e)
    (hpre : TracePre senv nDecl (Call.chain env e st))
    (v : (Call.chain env e st).Res)
    (hv : (chainStep senv env e st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.chain env e st) v) ∧ PhPost senv nDecl (Call.chain env e st) v

-- theorem mutants (well-typed single changes)
def MutEnvPhConsHandle : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal},
    EnvPh nDecl st env → EnvPh nDecl st (MachVal.handle 0 :: env)
def MutEnvPhConsNoH : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal},
    EnvPh nDecl st (MachVal.unit :: env)
def MutChainTraceNoHb : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (e : Lean.Expr) (st : MachRead),
      TracePre senv nDecl (Call.chain env e st) →
      ∀ (v : (Call.chain env e st).Res),
        (chainStep senv env e st).run (readF senv n) = some (some v) →
        FReachC nDecl st (callOut (Call.chain env e st) v) ∧ PhPost senv nDecl (Call.chain env e st) v
def MutChainTraceNoReach : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (e : Lean.Expr) (st : MachRead),
      ChainBasic e →
      TracePre senv nDecl (Call.chain env e st) →
      ∀ (v : (Call.chain env e st).Res),
        (chainStep senv env e st).run (readF senv n) = some (some v) →
        PhPost senv nDecl (Call.chain env e st) v
def MutChainTraceNoPhPost : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (e : Lean.Expr) (st : MachRead),
      ChainBasic e →
      TracePre senv nDecl (Call.chain env e st) →
      ∀ (v : (Call.chain env e st).Res),
        (chainStep senv env e st).run (readF senv n) = some (some v) →
        FReachC nDecl st (callOut (Call.chain env e st) v)
def MutChainTraceFuelSucc : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (e : Lean.Expr) (st : MachRead),
      ChainBasic e →
      TracePre senv nDecl (Call.chain env e st) →
      ∀ (v : (Call.chain env e st).Res),
        (chainStep senv env e st).run (readF senv (n + 1)) = some (some v) →
        FReachC nDecl st (callOut (Call.chain env e st) v) ∧ PhPost senv nDecl (Call.chain env e st) v

-- match-def mutants (well-typed single changes; compared by `exprAgree`)
def MutChainBasicLetE : Lean.Expr → Prop
  | .letE _ _ _ _ _ => True
  | .bvar _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .app _ _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .lit _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
def MutChainBasicApp : Lean.Expr → Prop
  | .letE _ _ _ _ _ => False
  | .bvar _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .app _ _ => False
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .lit _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True

end Expected

/-- The SAME per-constructor comparer for the real match def `f` and for every mutant `g`: both applied to a `Lean.Expr` built from fresh constructor arguments;
all 12 constructors must be defeq. Returns the failing constructors. -/
def exprAgree (f g : Name) : MetaM (List Name) := do
  let ctors : List Name := [``Lean.Expr.bvar, ``Lean.Expr.fvar, ``Lean.Expr.mvar, ``Lean.Expr.sort, ``Lean.Expr.const, ``Lean.Expr.app,
    ``Lean.Expr.lam, ``Lean.Expr.forallE, ``Lean.Expr.letE, ``Lean.Expr.lit, ``Lean.Expr.mdata, ``Lean.Expr.proj]
  let fTy ← inferType (mkConst f)
  let gTy ← inferType (mkConst g)
  unless (← isDefEq fTy gTy) do throwError "GEN5 CHAINCHECK exprAgree: signatures of {f} and {g} differ"
  let mut bad : List Name := []
  for ctor in ctors do
    let ok ← forallTelescope (← inferType (mkConst ctor)) fun cargs _ => do
      let c := mkAppN (mkConst ctor) cargs
      withoutModifyingState (isDefEq (mkApp (mkConst f) c) (mkApp (mkConst g) c))
    unless ok do bad := bad ++ [ctor]
  pure bad

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``envPh_cons_unit ``ExpEnvPhConsUnit
  checkExpected ``chain_basic_trace ``ExpChainBasicTrace
  logInfo m!"GEN5 CHAINCHECK TYPE 2 theorems compared (envPh_cons_unit, chain_basic_trace)"
  let bad ← exprAgree ``ChainBasic ``ExpChainBasic
  unless bad.isEmpty do throwError "GEN5 CHAINCHECK CHECK FAILED: ChainBasic disagrees with ExpChainBasic at {bad}"
  logInfo m!"GEN5 CHAINCHECK TYPE 1 match def (ChainBasic) x 12 constructors agrees with the independent version; whole-domain agreement is the theorem chainBasic_eq_exp"
  checkMutant ``envPh_cons_unit ``MutEnvPhConsHandle
  checkMutant ``envPh_cons_unit ``MutEnvPhConsNoH
  checkMutant ``chain_basic_trace ``MutChainTraceNoHb
  checkMutant ``chain_basic_trace ``MutChainTraceNoReach
  checkMutant ``chain_basic_trace ``MutChainTraceNoPhPost
  checkMutant ``chain_basic_trace ``MutChainTraceFuelSucc
  logInfo m!"GEN5 CHAINCHECK MUTANT 6 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"
  let mm : List (Name × Name × List Name) :=
    [ (``MutChainBasicLetE, ``ExpChainBasic, [``Lean.Expr.letE]),
      (``MutChainBasicApp, ``ExpChainBasic, [``Lean.Expr.app]) ]
  let mut nm : Nat := 0
  for (g, ex, expectBad) in mm do
    let bad ← exprAgree g ex
    unless bad == expectBad do throwError "GEN5 CHAINCHECK MATCHDEF MUTANT ACCEPTED/UNEXPECTED: {g} disagrees at {bad}, expected {expectBad}"
    nm := nm + 1
  logInfo m!"GEN5 CHAINCHECK MATCHDEF MUTANT {nm} well-typed match-def mutants each rejected at exactly the changed constructor (signature/defeq rejection, not a semantic counterexample); with the 6 theorem mutants: 8"

def newThms : List Name := [``envPh_cons_unit, ``chain_basic_trace]
def newDefs : List Name := [``ChainBasic]
def allThms : List Name := newThms ++ [``chainBasic_eq_exp]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n
  logInfo m!"GEN5 CHAINCHECK AXIOMS {allThms.length} theorems checked (standard axioms only)"

def closureRoots : List Name := newDefs ++ allThms

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
    addDecl (.thmDecl { name := `ReaderTraceChain.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceChain.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceChain.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceChain.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceChain.direct, `ReaderTraceChain.viaHelper, `ReaderTraceChain.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 CHAINCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 CHAINCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceChain.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 CHAINCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 CHAINCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceChain.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceChain.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceChain.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceChain.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceChain.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceChain.Missing.nowhere do throwError "GEN5 CHAINCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceChain.viaHelperU, `ReaderTraceChain.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceChain.Missing.nowhere do throwError "GEN5 CHAINCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceChain.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 CHAINCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 CHAINCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newDefs.length == 1 && newThms.length == 2 do throwError "GEN5 CHAINCHECK CLOSURE FAILED: expected 1 def + 2 theorems"
  for n in newDefs ++ newThms do
    unless seen.contains n do throwError "GEN5 CHAINCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 CHAINCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 CHAINCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 CHAINCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 CHAINCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (1 def + 2 theorems + 1 agreement theorem); all 3 target declarations (1 def + 2 theorems) in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceChainCheck
