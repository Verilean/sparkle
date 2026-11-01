import Tools.ShippingGen5ReaderTraceNested
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceNestedCheck, exit 0; TYPE 3 theorems; MUTANT 7 theorem-statement mutants (signature/defeq rejections, not semantic counterexamples); AXIOMS 3 (standard only); CLOSURE OK 4721 constants from 3 roots, 3 targets seen; 3 intended in-memory sorry negatives print warnings) on the tree of b3e517dfe919fb1424122e223aef8abe56b79456 (Lean content identical; this header is comment-only). Written against freeze rev10 addendum §3 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R6). No sorry / axiom / native_decide in source; the closure-control negatives are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R6 checks (Tools/ShippingGen5ReaderTraceNested.lean)

TYPE: the three frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceNestedCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
  Tools.ShippingReaderLenOk

section Expected

def ExpReserved : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    {dom' : Lean.Expr} (hdr : InRange nDecl s s.lets.size dom') (hdn : NoLoose 0 dom')
    (body : Lean.Expr) (kinds : List MixedGateBinder) (inits : List Nat),
    FReachC nDecl s (reserved s dom' body kinds inits) ∧ TrInv senv nDecl (reserved s dom' body kinds inits)
def ExpPushNested : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (ob : Bool) (e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)
    (hv : InRange nDecl s s.lets.size e.2.2.2.2.2) (hn : NoLoose 0 e.2.2.2.2.2),
    FReachC nDecl s { s with inInner := ob, nested := s.nested.push e } ∧
    TrInv senv nDecl { s with inInner := ob, nested := s.nested.push e }
def ExpNested : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.nested env dom αs initsE body st))
    (r : (Call.nested env dom αs initsE body st).Res)
    (hv : (nestedStep senv env dom αs initsE body st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.nested env dom αs initsE body st) r) ∧
    PhPost senv nDecl (Call.nested env dom αs initsE body st) r

def MutReservedNoHdn : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    {dom' : Lean.Expr} (hdr : InRange nDecl s s.lets.size dom')
    (body : Lean.Expr) (kinds : List MixedGateBinder) (inits : List Nat),
    FReachC nDecl s (reserved s dom' body kinds inits) ∧ TrInv senv nDecl (reserved s dom' body kinds inits)
def MutReservedNoReach : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    {dom' : Lean.Expr} (hdr : InRange nDecl s s.lets.size dom') (hdn : NoLoose 0 dom')
    (body : Lean.Expr) (kinds : List MixedGateBinder) (inits : List Nat),
    TrInv senv nDecl (reserved s dom' body kinds inits)
def MutPushNestedNoHn : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (ob : Bool) (e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)
    (hv : InRange nDecl s s.lets.size e.2.2.2.2.2),
    FReachC nDecl s { s with inInner := ob, nested := s.nested.push e } ∧
    TrInv senv nDecl { s with inInner := ob, nested := s.nested.push e }
def MutPushNestedNoInner : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)
    (hv : InRange nDecl s s.lets.size e.2.2.2.2.2) (hn : NoLoose 0 e.2.2.2.2.2),
    FReachC nDecl s { s with nested := s.nested.push e } ∧
    TrInv senv nDecl { s with nested := s.nested.push e }
def MutNestedNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.nested env dom αs initsE body st))
    (r : (Call.nested env dom αs initsE body st).Res)
    (hv : (nestedStep senv env dom αs initsE body st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.nested env dom αs initsE body st) r
def MutNestedNoHpre : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
    (r : (Call.nested env dom αs initsE body st).Res)
    (hv : (nestedStep senv env dom αs initsE body st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.nested env dom αs initsE body st) r) ∧
    PhPost senv nDecl (Call.nested env dom αs initsE body st) r
def MutNestedNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.nested env dom αs initsE body st))
    (r : (Call.nested env dom αs initsE body st).Res)
    (hv : (nestedStep senv env dom αs initsE body st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.nested env dom αs initsE body st) r) ∧
    PhPost senv nDecl (Call.nested env dom αs initsE body st) r

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``trInv_reserved ``ExpReserved
  checkExpected ``trInv_pushNested ``ExpPushNested
  checkExpected ``nested_trace ``ExpNested
  logInfo m!"GEN5 NESTEDCHECK TYPE 3 theorems compared"
  checkMutant ``trInv_reserved ``MutReservedNoHdn
  checkMutant ``trInv_reserved ``MutReservedNoReach
  checkMutant ``trInv_pushNested ``MutPushNestedNoHn
  checkMutant ``trInv_pushNested ``MutPushNestedNoInner
  checkMutant ``nested_trace ``MutNestedNoReach
  checkMutant ``nested_trace ``MutNestedNoHpre
  checkMutant ``nested_trace ``MutNestedNoHT
  logInfo m!"GEN5 NESTEDCHECK MUTANT 7 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``trInv_reserved, ``trInv_pushNested, ``nested_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 NESTEDCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceNestedCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceNestedCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceNestedCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceNestedCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceNestedCheck.direct, `ReaderTraceNestedCheck.viaHelper, `ReaderTraceNestedCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 NESTEDCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 NESTEDCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceNestedCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 NESTEDCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 NESTEDCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceNestedCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceNestedCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceNestedCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceNestedCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceNestedCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceNestedCheck.Missing.nowhere do throwError "GEN5 NESTEDCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceNestedCheck.viaHelperU, `ReaderTraceNestedCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceNestedCheck.Missing.nowhere do throwError "GEN5 NESTEDCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceNestedCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 NESTEDCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 NESTEDCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 3 do throwError "GEN5 NESTEDCHECK CLOSURE FAILED: expected 3 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 NESTEDCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 NESTEDCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 NESTEDCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 NESTEDCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 NESTEDCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (3 theorems); all 3 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceNestedCheck
