/-
  Equivalence — One-line BitVec equivalence checks via `bv_decide`.

  Adds a single command, `#verify_eq f g`, that:
    1. Resolves two existing top-level `def`s `f` and `g`.
    2. Introspects their arity and checks their types agree.
    3. Generates a fresh theorem `{f}_eq_{g} : f = g` and discharges it
       with `funext` (as many times as needed) + `unfold f g` + `bv_decide`.
    4. Logs ✅ success or ❌ failure (passing through `bv_decide`'s
       counterexample verbatim).

  Intended for pure `BitVec a → … → BitVec z` functions at small widths.
  No Signal DSL / temporal / multi-cycle equivalence in v1 — see plan §I.

  ⚠  KNOWN ISSUE (docs/KnownIssues.md Issue 2): `bv_decide` hangs in
  `lake build` compilation mode on Lean 4.28.0-rc1, but works in the
  interpreter (`lake env lean`) and in VSCode. This module ITSELF never
  calls `bv_decide` — it only defines the elaborator — so it is always
  safe to `lake build`. Files that CALL `#verify_eq` (e.g.
  `Tests/Verification/EquivDemo.lean`) must be run interactively and
  should not be imported from the default `lake build` target.

  Usage:

      def pure_alu (a b : BitVec 8) : BitVec 8 := a + b
      def fast_alu (a b : BitVec 8) : BitVec 8 :=
        (a ^^^ b) + ((a &&& b) <<< 1)
      #verify_eq fast_alu pure_alu
-/

import Lean
import Lean.Meta
import Lean.Elab.Command

namespace Sparkle.Verification.Equivalence

open Lean Elab Command Meta

/-- Count the number of leading `∀` / Pi binders in a function type.
    Used to decide how many `funext`s to emit in the generated proof. -/
private def arityOfType (t : Expr) : MetaM Nat := do
  forallTelescopeReducing t fun args _ => pure args.size

/-- `#verify_eq f g` — prove `f = g` via `funext; unfold; bv_decide`. -/
syntax (name := verifyEqCmd) "#verify_eq " ident ident : command

@[command_elab verifyEqCmd]
def elabVerifyEq : CommandElab := fun stx => do
  match stx with
  | `(#verify_eq $f:ident $g:ident) => do
    -- 1. Resolve both idents to fully-qualified names.
    let fName ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo f)
    let gName ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo g)

    -- 2. Introspect types, verify they match, compute arity.
    let (arity, _) ← liftTermElabM do
      let fInfo ← getConstInfo fName
      let gInfo ← getConstInfo gName
      let fT := fInfo.type
      let gT := gInfo.type
      unless (← isDefEq fT gT) do
        throwErrorAt g
          m!"#verify_eq: type mismatch{indentD m!"{f} : {fT}"}{indentD m!"{g} : {gT}"}"
      let n ← arityOfType fT
      pure (n, fT)

    -- 3. Fresh theorem name. Reject if it already exists to avoid
    --    surprising shadowing.
    let thmBase := Name.mkSimple s!"{fName.toString}_eq_{gName.toString}"
    let thmName := thmBase.replacePrefix .anonymous .anonymous
    if (← getEnv).contains thmName then
      throwError m!"#verify_eq: theorem `{thmName}` already exists; \
                    delete it or rename one of `{fName}` / `{gName}`"
    let thmIdent := mkIdent thmName

    -- 4. Build fresh binder idents `x_1, …, x_n`.
    let binders : Array (TSyntax `ident) :=
      (Array.range arity).map fun i =>
        mkIdent (Name.mkSimple s!"x_{i + 1}")

    -- 5. Build the theorem via quotation. Zero arity → skip funext.
    let cmd ← if arity == 0 then
      `(command|
        theorem $thmIdent : $f = $g := by
          unfold $f:ident $g:ident
          bv_decide)
    else
      `(command|
        theorem $thmIdent : $f = $g := by
          funext $binders*
          unfold $f:ident $g:ident
          bv_decide)

    -- 6. Elaborate the theorem command and decide success/failure.
    --    `elabCommand` does NOT re-throw tactic errors like `bv_decide`'s
    --    "counterexample found" — those are deferred via the message log
    --    and surface as separate errors at the command position. We
    --    therefore detect success by
    --      (a) try/catch around elabCommand (for pre-elab failures), and
    --      (b) checking both the message log AND the environment: if the
    --          proof failed, the theorem is either missing or sorry-axiom
    --          tainted.
    let msgsBefore := (← get).messages
    let thrown ← try elabCommand cmd; pure false
                 catch _ => pure true
    let msgsAfter := (← get).messages
    let newErrors :=
      (msgsAfter.toList.drop msgsBefore.toList.length).filter
        (·.severity == .error)
    let tainted :=
      match (← getEnv).find? thmName with
      | none => true
      | some ci => ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false
    if thrown || !newErrors.isEmpty || tainted then
      logInfoAt f
        m!"❌ `#verify_eq {fName} {gName}` — see error(s) above for `{thmName}`"
    else
      logInfoAt f
        m!"✅ verified: `{thmName}` — `{fName}` ≡ `{gName}`"

  | _ => throwUnsupportedSyntax

end Sparkle.Verification.Equivalence
