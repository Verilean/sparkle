import Tools.ShippingGen5ReaderTraceExtract
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT yet (pending Pod build). Written against freeze `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §2; clean issue-linked build pending (coder). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4e1 checks (Tools/ShippingGen5ReaderTraceExtract.lean)

TYPE: the five frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); the three helpers (`inlSpine_ph0`, `argsAcc_length_of_arity`, `getAppArgs_size_of_arity`) are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceExtractCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv 

section Expected

def ExpSpine : Prop := ∀ {L : Nat} (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) → ∀ a ∈ (inlSpine e acc).2, NoPh a = true ∧ BvarLt L a = true
def ExpInstCall : Prop := ∀ {L : Nat} {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machInstCall? senv e = some (c, kinds, res, args)), ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true
def ExpInstCallS : Prop := ∀ {L : Nat} {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machInstCallS? senv e = some (c, kinds, ty, args)), ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true
def ExpRunApp : Prop := ∀ {L : Nat} {e dom αs inits body : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machRunApp? e = some (dom, αs, inits, body)),
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh αs = true ∧ BvarLt L αs = true) ∧
    (NoPh inits = true ∧ BvarLt L inits = true) ∧ (NoPh body = true ∧ BvarLt (L + 1) body = true)
def ExpMemCall : Prop := ∀ {L : Nat} {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool} {aw dw : Nat}
    {dom : Lean.Expr} {ops : List Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)),
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ ∀ a ∈ ops, NoPh a = true ∧ BvarLt L a = true

-- theorem mutants (well-typed single changes)

def MutSpineNoAcc : Prop := ∀ {L : Nat} (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    ∀ a ∈ (inlSpine e acc).2, NoPh a = true ∧ BvarLt L a = true
def MutSpineNoPhOnly : Prop := ∀ {L : Nat} (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) → ∀ a ∈ (inlSpine e acc).2, NoPh a = true
def MutInstCallNoHn : Prop := ∀ {L : Nat} {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr}, BvarLt L e = true →
    machInstCall? senv e = some (c, kinds, res, args) → ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true
def MutInstCallSNoHb : Prop := ∀ {L : Nat} {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr}, NoPh e = true →
    machInstCallS? senv e = some (c, kinds, ty, args) → ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true
def MutRunAppBodyL : Prop := ∀ {L : Nat} {e dom αs inits body : Lean.Expr}, NoPh e = true → BvarLt L e = true →
    machRunApp? e = some (dom, αs, inits, body) →
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh αs = true ∧ BvarLt L αs = true) ∧
    (NoPh inits = true ∧ BvarLt L inits = true) ∧ (NoPh body = true ∧ BvarLt L body = true)
def MutRunAppNoBody : Prop := ∀ {L : Nat} {e dom αs inits body : Lean.Expr}, NoPh e = true → BvarLt L e = true →
    machRunApp? e = some (dom, αs, inits, body) →
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh αs = true ∧ BvarLt L αs = true) ∧
    (NoPh inits = true ∧ BvarLt L inits = true)
def MutMemCallNoDom : Prop := ∀ {L : Nat} {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool} {aw dw : Nat}
    {dom : Lean.Expr} {ops : List Lean.Expr}, NoPh e = true → BvarLt L e = true →
    Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops) →
    ∀ a ∈ ops, NoPh a = true ∧ BvarLt L a = true
def MutMemCallLPlus : Prop := ∀ {L : Nat} {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool} {aw dw : Nat}
    {dom : Lean.Expr} {ops : List Lean.Expr}, NoPh e = true → BvarLt L e = true →
    Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops) →
    (NoPh dom = true ∧ BvarLt (L + 1) dom = true) ∧ ∀ a ∈ ops, NoPh a = true ∧ BvarLt (L + 1) a = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``inlSpine_ph ``ExpSpine
  checkExpected ``machInstCall?_ph ``ExpInstCall
  checkExpected ``machInstCallS?_args_ph ``ExpInstCallS
  checkExpected ``machRunApp?_ph ``ExpRunApp
  checkExpected ``memCall?_ph ``ExpMemCall
  logInfo m!"GEN5 EXTRACTCHECK TYPE 5 theorems compared"
  checkMutant ``inlSpine_ph ``MutSpineNoAcc
  checkMutant ``inlSpine_ph ``MutSpineNoPhOnly
  checkMutant ``machInstCall?_ph ``MutInstCallNoHn
  checkMutant ``machInstCallS?_args_ph ``MutInstCallSNoHb
  checkMutant ``machRunApp?_ph ``MutRunAppBodyL
  checkMutant ``machRunApp?_ph ``MutRunAppNoBody
  checkMutant ``memCall?_ph ``MutMemCallNoDom
  checkMutant ``memCall?_ph ``MutMemCallLPlus
  logInfo m!"GEN5 EXTRACTCHECK MUTANT 8 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``inlSpine_ph, ``inlSpine_ph0, ``machInstCall?_ph, ``machInstCallS?_args_ph, ``machRunApp?_ph,
  ``argsAcc_length_of_arity, ``getAppArgs_size_of_arity, ``memCall?_ph]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 EXTRACTCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceExtractCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceExtractCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceExtractCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceExtractCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceExtractCheck.direct, `ReaderTraceExtractCheck.viaHelper, `ReaderTraceExtractCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 EXTRACTCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 EXTRACTCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceExtractCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 EXTRACTCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 EXTRACTCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceExtractCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceExtractCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceExtractCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceExtractCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceExtractCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceExtractCheck.Missing.nowhere do throwError "GEN5 EXTRACTCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceExtractCheck.viaHelperU, `ReaderTraceExtractCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceExtractCheck.Missing.nowhere do throwError "GEN5 EXTRACTCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceExtractCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 EXTRACTCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 EXTRACTCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 8 do throwError "GEN5 EXTRACTCHECK CLOSURE FAILED: expected 8 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 EXTRACTCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 EXTRACTCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 EXTRACTCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 EXTRACTCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 EXTRACTCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (8 theorems); all 8 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceExtractCheck
