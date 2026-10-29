import Lean
set_option autoImplicit false
-- Built here: g3sv-b5be62e6. LOCAL COPY (scripts/gen2/SERVED_FREEZE.md rev1 §4.2) of `par/gen2-spec`
-- Tests/Gen3/ExpectedType.lean (read at e134c63a; built there as g3dsc-1b840215). The text below the namespace
-- line is identical to the source except the namespace name (`Tests.Gen3.ServedExpectedType`, so that both files
-- can be imported together after integration). At integration this copy is deleted and the check file imports
-- `Tests.Gen3.ExpectedType`.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # Mechanical expected-type comparison for the gen3 data-supply units

The style of Tests/Gen2/PMem4Check.lean §1, as a small shared helper:

* `stmtOf n`: the TYPE of a theorem, or the VALUE of a definition (an independent `Expected…` statement written as
  `def … : Prop := ∀ …, …`, or the body `fun … => …` of a definition under test).
* `cmpTele`: both sides are walked binder by binder (`∀` against `∀`, `fun` against `fun`); each pair must have the same
  name (macro scopes erased), the same binder info and the same type, and the bodies are instantiated with the SAME
  fresh fvar. Types and the final body are compared with `==` after `instantiateMVars`; on a syntactic mismatch a
  `GEN3 NOTE` is logged and `isDefEq` is the fallback (logged as `GEN3 DEFEQ`); anything else throws `GEN3 CHECK FAILED`.
* `checkExpected thm exp`: `cmpTele` on `stmtOf thm` / `stmtOf exp`, plus equal universe parameters.
* `checkMutant thm mut`: the comparison MUST FAIL (a meaning-changing mutant of the expected statement is rejected);
  also the whole statements must not be `isDefEq`. If it is accepted, throws `GEN3 MUTANT ACCEPTED`.
* `checkAxioms n`: `Lean.collectAxioms n ⊆ [propext, Classical.choice, Quot.sound]`, else throws. -/

namespace Tests.Gen3.ServedExpectedType
open Lean Meta

/-- The statement of `n`: a theorem's type, or a definition's value. -/
def stmtOf (n : Name) : MetaM Expr := do
  match ← getConstInfo n with
  | .thmInfo t => pure t.type
  | .defnInfo d => pure d.value
  | _ => throwError "GEN3 CHECK FAILED: {n} is neither a theorem nor a definition"

/-- `==` after `instantiateMVars`; on a mismatch log it and fall back to `isDefEq` (logged); else fail. -/
def cmpEq (what : String) (a e : Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  logInfo m!"GEN3 NOTE {what}: not syntactically equal, trying isDefEq:{indentExpr a}\nexpected{indentExpr e}"
  if (← isDefEq a e) then
    logInfo m!"GEN3 DEFEQ {what}: accepted by isDefEq (NOT syntactic)"
  else
    throwError "GEN3 CHECK FAILED {what}:{indentExpr a}\nexpected{indentExpr e}"

/-- Binder-by-binder comparison of two `∀`/`fun` telescopes (see the module doc). -/
partial def cmpTele (what : String) (a e : Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do
      throwError "GEN3 CHECK FAILED {what}: binder {i} is named {na}, expected {ne}"
    unless bia == bie do
      throwError "GEN3 CHECK FAILED {what}: binder {i} ({na}) has a different binder info"
    cmpEq s!"{what} binder {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTele what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .lam na ta ba bia, .lam ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do
      throwError "GEN3 CHECK FAILED {what}: parameter {i} is named {na}, expected {ne}"
    unless bia == bie do
      throwError "GEN3 CHECK FAILED {what}: parameter {i} ({na}) has a different binder info"
    cmpEq s!"{what} parameter {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTele what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .forallE na .., _ =>
    throwError "GEN3 CHECK FAILED {what}: extra binder {i} ({na}) not in the expected statement"
  | _, .forallE ne .. =>
    throwError "GEN3 CHECK FAILED {what}: expected binder {i} ({ne}) is missing"
  | _, _ => cmpEq s!"{what} conclusion" a e

/-- `thm`'s statement equals the independent expected statement `exp`. -/
def checkExpected (thm exp : Name) : MetaM Unit := do
  let ciT ← getConstInfo thm
  let ciE ← getConstInfo exp
  unless ciT.levelParams.length == ciE.levelParams.length do
    throwError "GEN3 CHECK FAILED {thm}: universe parameters {ciT.levelParams} vs {ciE.levelParams}"
  let a ← stmtOf thm
  let e ← stmtOf exp
  let e := e.instantiateLevelParams ciE.levelParams (ciT.levelParams.map mkLevelParam)
  cmpTele s!"{thm}" a e
  logInfo m!"GEN3 TYPE OK {thm} against {exp}"

/-- The mutant `mt` must NOT be accepted as `thm`'s statement. -/
def checkMutant (thm mt : Name) : MetaM Unit := do
  let a ← stmtOf thm
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTele s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then
    throwError "GEN3 MUTANT ACCEPTED: {mt} matches {thm}"
  if (← withoutModifyingState (isDefEq a e)) then
    throwError "GEN3 MUTANT ACCEPTED (isDefEq of the whole statements): {mt} vs {thm}"
  logInfo m!"GEN3 MUTANT REJECTED {mt} (against {thm})"

/-- Only the standard axioms. -/
def checkAxioms (n : Name) : MetaM Unit := do
  let ax ← Lean.collectAxioms n
  for a in ax do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "GEN3 CHECK FAILED {n}: uses the axiom {a}"
  logInfo m!"GEN3 AXIOMS OK {n}: {ax}"

end Tests.Gen3.ServedExpectedType
