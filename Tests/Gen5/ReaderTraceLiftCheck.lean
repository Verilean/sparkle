import Tools.ShippingGen5ReaderTraceLift
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceLiftCheck, exit 0; TYPE 4 theorems; MUTANT 7 theorem-statement mutants (signature/defeq rejections, not semantic counterexamples); AXIOMS 4 (standard only); CLOSURE OK 1674 constants from 4 roots, 4 targets seen; 3 intended in-memory sorry negatives print warnings) on the tree of c7e641ff982b816588e1d48891590bb83fe50199 (Lean content identical; this header is comment-only). Written against freeze `scripts/gen5/DG_READERTRACE_FREEZE_REV7.md` §2; clean issue-linked build pending (coder). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4c part 2 checks (Tools/ShippingGen5ReaderTraceLift.lean)

TYPE: the frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); helpers are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceLiftCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv 

section Expected

def ExpLiftNoPh : Prop := ∀ (e : Lean.Expr) (s d : Nat), NoPh e = true → NoPh (liftSpec e s d) = true
def ExpLiftBvar : Prop := ∀ (e : Lean.Expr) (s d L : Nat), BvarLt L e = true → BvarLt (L + d) (liftSpec e s d) = true
def ExpRootNoPh : Prop := ∀ e : Lean.Expr, NoPh e = true → NoPh (rootFloatS e) = true
def ExpRootBvar : Prop := ∀ (e : Lean.Expr) (L : Nat), BvarLt L e = true → BvarLt L (rootFloatS e) = true

-- theorem mutants (well-typed single changes)

def MutLiftNoPhId : Prop := ∀ (e : Lean.Expr) (s d : Nat), NoPh e = true → NoPh e = true
def MutLiftBvarL : Prop := ∀ (e : Lean.Expr) (s d L : Nat), BvarLt L e = true → BvarLt L (liftSpec e s d) = true
def MutLiftBvarLs : Prop := ∀ (e : Lean.Expr) (s d L : Nat), BvarLt L e = true → BvarLt (L + s) (liftSpec e s d) = true
def MutLiftBvarNoHyp : Prop := ∀ (e : Lean.Expr) (s d L : Nat), BvarLt (L + d) (liftSpec e s d) = true
def MutRootNoPhRev : Prop := ∀ e : Lean.Expr, NoPh (rootFloatS e) = true → NoPh e = true
def MutRootBvarL1 : Prop := ∀ (e : Lean.Expr) (L : Nat), BvarLt L e = true → BvarLt (L + 1) (rootFloatS e) = true
def MutRootBvarLower : Prop := ∀ (e : Lean.Expr) (L : Nat), BvarLt (L + 1) e = true → BvarLt L (rootFloatS e) = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``liftSpec_noPh ``ExpLiftNoPh
  checkExpected ``liftSpec_bvarLt ``ExpLiftBvar
  checkExpected ``rootFloatS_noPh ``ExpRootNoPh
  checkExpected ``rootFloatS_bvarLt ``ExpRootBvar
  logInfo m!"GEN5 LIFTCHECK TYPE 4 theorems compared"
  checkMutant ``liftSpec_noPh ``MutLiftNoPhId
  checkMutant ``liftSpec_bvarLt ``MutLiftBvarL
  checkMutant ``liftSpec_bvarLt ``MutLiftBvarLs
  checkMutant ``liftSpec_bvarLt ``MutLiftBvarNoHyp
  checkMutant ``rootFloatS_noPh ``MutRootNoPhRev
  checkMutant ``rootFloatS_bvarLt ``MutRootBvarL1
  checkMutant ``rootFloatS_bvarLt ``MutRootBvarLower
  logInfo m!"GEN5 LIFTCHECK MUTANT 7 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``liftSpec_noPh, ``liftSpec_bvarLt, ``rootFloatS_noPh, ``rootFloatS_bvarLt]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 LIFTCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceLiftCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceLiftCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceLiftCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceLiftCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceLiftCheck.direct, `ReaderTraceLiftCheck.viaHelper, `ReaderTraceLiftCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 LIFTCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 LIFTCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceLiftCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 LIFTCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 LIFTCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceLiftCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceLiftCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceLiftCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceLiftCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceLiftCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceLiftCheck.Missing.nowhere do throwError "GEN5 LIFTCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceLiftCheck.viaHelperU, `ReaderTraceLiftCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceLiftCheck.Missing.nowhere do throwError "GEN5 LIFTCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceLiftCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 LIFTCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 LIFTCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 4 do throwError "GEN5 LIFTCHECK CLOSURE FAILED: expected 4 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 LIFTCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 LIFTCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 LIFTCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 LIFTCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 LIFTCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (4 theorems); all 4 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceLiftCheck
