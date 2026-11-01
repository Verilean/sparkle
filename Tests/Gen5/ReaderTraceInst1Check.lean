import Tools.ShippingGen5ReaderTraceInst1
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT yet (pending Pod build). Written against freeze `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §1; clean issue-linked build pending (coder). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE Inst1Ph checks (Tools/ShippingGen5ReaderTraceInst1.lean)

TYPE: the frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); `Inst1Ph` is a def, so it is checked through `inst1Ph_of_agrees`.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceInst1Check
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv 

section Expected

def ExpInst1NoPh : Prop := ∀ (b a : Lean.Expr) (off : Nat), NoPh b = true → NoPh a = true → NoPh (inst1Spec b a off) = true
def ExpInst1Bvar : Prop := ∀ (b a : Lean.Expr) (off m m' : Nat), BvarLt (m + 1 + off) b = true →
    BvarLt m' a = true → m ≤ m' → BvarLt (m' + off) (inst1Spec b a off) = true
def ExpInst1PhBody : Prop := ∀ (b a : Lean.Expr) (m m' : Nat), NoPh b = true → NoPh a = true →
    BvarLt (m + 1) b = true → BvarLt m' a = true → m ≤ m' →
    NoPh (b.instantiate1 a) = true ∧ BvarLt m' (b.instantiate1 a) = true
def ExpInst1Ph : Prop := ∀ (h : Inst1Agrees), Inst1Ph
-- the def `Inst1Ph` is exactly the frozen body (checked by defeq)
example : Inst1Ph = ExpInst1PhBody := rfl

-- theorem mutants (well-typed single changes)

def MutInst1NoPhNoHa : Prop := ∀ (b a : Lean.Expr) (off : Nat), NoPh b = true → NoPh (inst1Spec b a off) = true
def MutInst1BvarNoLe : Prop := ∀ (b a : Lean.Expr) (off m m' : Nat), BvarLt (m + 1 + off) b = true →
    BvarLt m' a = true → BvarLt (m' + off) (inst1Spec b a off) = true
def MutInst1BvarNoSucc : Prop := ∀ (b a : Lean.Expr) (off m m' : Nat), BvarLt (m + off) b = true →
    BvarLt m' a = true → m ≤ m' → BvarLt (m' + off) (inst1Spec b a off) = true
def MutInst1BvarLow : Prop := ∀ (b a : Lean.Expr) (off m m' : Nat), BvarLt (m + 1 + off) b = true →
    BvarLt m' a = true → m ≤ m' → BvarLt (m + off) (inst1Spec b a off) = true
def MutInst1PhNoAgrees : Prop := ExpInst1PhBody
def MutInst1PhNoLe : Prop := ∀ (h : Inst1Agrees), ∀ (b a : Lean.Expr) (m m' : Nat), NoPh b = true → NoPh a = true →
    BvarLt (m + 1) b = true → BvarLt m' a = true →
    NoPh (b.instantiate1 a) = true ∧ BvarLt m' (b.instantiate1 a) = true
def MutInst1PhOnlyNoPh : Prop := ∀ (h : Inst1Agrees), ∀ (b a : Lean.Expr) (m m' : Nat), NoPh b = true → NoPh a = true →
    BvarLt (m + 1) b = true → BvarLt m' a = true → m ≤ m' → NoPh (b.instantiate1 a) = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``inst1Spec_noPh ``ExpInst1NoPh
  checkExpected ``inst1Spec_bvarLt ``ExpInst1Bvar
  checkExpected ``inst1Ph_of_agrees ``ExpInst1Ph
  logInfo m!"GEN5 INST1CHECK TYPE 3 theorems compared"
  checkMutant ``inst1Spec_noPh ``MutInst1NoPhNoHa
  checkMutant ``inst1Spec_bvarLt ``MutInst1BvarNoLe
  checkMutant ``inst1Spec_bvarLt ``MutInst1BvarNoSucc
  checkMutant ``inst1Spec_bvarLt ``MutInst1BvarLow
  checkMutant ``inst1Ph_of_agrees ``MutInst1PhNoAgrees
  checkMutant ``inst1Ph_of_agrees ``MutInst1PhNoLe
  checkMutant ``inst1Ph_of_agrees ``MutInst1PhOnlyNoPh
  logInfo m!"GEN5 INST1CHECK MUTANT 7 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``inst1Spec_noPh, ``inst1Spec_bvarLt, ``inst1Ph_of_agrees]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 INST1CHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceInst1Check.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceInst1Check.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceInst1Check.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceInst1Check.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceInst1Check.direct, `ReaderTraceInst1Check.viaHelper, `ReaderTraceInst1Check.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 INST1CHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 INST1CHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceInst1Check.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 INST1CHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 INST1CHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceInst1Check.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInst1Check.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInst1Check.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceInst1Check.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceInst1Check.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceInst1Check.Missing.nowhere do throwError "GEN5 INST1CHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceInst1Check.viaHelperU, `ReaderTraceInst1Check.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceInst1Check.Missing.nowhere do throwError "GEN5 INST1CHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceInst1Check.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 INST1CHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 INST1CHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 3 do throwError "GEN5 INST1CHECK CLOSURE FAILED: expected 3 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 INST1CHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 INST1CHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 INST1CHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 INST1CHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 INST1CHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (3 theorems); all 3 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceInst1Check
