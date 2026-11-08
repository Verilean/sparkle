import Lean

/-!
# Strict axiom audit for the `#verify_elab_deep` extension (U0/U1)

Reviewer ruling 2026-11-08 (items 8 and 9): the strict route accepts a
declaration only if the REACHABLE axiom closure of that declaration is a
subset of the three standard axioms

  `propext`, `Classical.choice`, `Quot.sound`.

The decision is made on the closure computed by `Lean.collectAxioms`, never
on tactic names and never on name patterns.  In particular the following are
rejected whatever their names look like:

* `Lean.ofReduceBool`, `Lean.trustCompiler` (compiler trust),
* any `*._native.native_decide.ax_*` / `*._native.bv_decide.ax_*` auxiliary,
* `sorryAx`,
* any user `axiom`, including one named `ax_…` or placed under `_native`.

This file deliberately does NOT reuse the shared-route allowance of
`Tools/DeepElab.lean` (`isAux`, the name-pattern match on
`.str (.str (.str _ "_native") "native_decide") ax`); the ruling rejects
copying it, because an arbitrary axiom can be given such a name.

Besides the axiom closure, the audit checks that the declaration exists, is a
`theorem` (not a `def`, `axiom`, `opaque`, …), and that neither its type nor
its proof term contains metavariables.

`#ved_axioms_raw d` is a MEASUREMENT command for the U0 harness: it prints the
raw closure without judging it.  Its output is not a strict acceptance.

## What the enumeration commands do NOT audit

`#ved_audit_generated Ns` and `#ved_audit_current_namespace` only ENUMERATE
the theorems declared in the current file under a namespace and report each
one's strict verdict and raw closure.  They do NOT audit

* that every EXPECTED theorem was generated (a missing theorem simply does not
  appear; the U0 classifier compares the found names against the per-output,
  per-stage required set, and that set is itself only an observation of the
  second synthesis run),
* that a theorem's STATEMENT is the right one (its type is not compared with
  any expected type; the contract is not checked), nor
* that the module a theorem is about is the artifact a command returned.

`strictAudit` on one declaration is the acceptance step for that declaration's
axiom closure only; the contract (U1) is a separate obligation.

## Synchronous registration

The U0 harness puts `set_option Elab.async false in` in front of the measured
`#verify_elab_deep` (which also elaborates every generated theorem
synchronously itself), so a kernel-rejected theorem is ABSENT when these
commands enumerate.  That is a property of the U0 case files.  When the
commands are used elsewhere, they see only the theorems that are already in
the environment at that point: under asynchronous elaboration (the Lean
default) a theorem whose proof is still being checked, or will later be
rejected, may be listed or missing.  General use therefore REQUIRES the
caller to elaborate the audited declarations synchronously (or to audit after
the file is complete); these commands do not enforce it.
-/

namespace Tools.VedStrictAudit

open Lean Elab Command

/-- The strict allowed set: exactly the three standard axioms. -/
def strictAllowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- One-line rendering of a name list (no message-layout line breaks). -/
def showNames (xs : Array Name) : String :=
  "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"

/-- Deterministic order for reports. -/
def sortNames (xs : Array Name) : Array Name :=
  xs.qsort fun a b => a.toString < b.toString

/-- The axioms of a closure that are outside the strict set.  Membership in
`strictAllowed` is the ONLY criterion: there is no name-pattern exception. -/
def offendingOf (axs : Array Name) : Array Name :=
  sortNames (axs.filter fun a => !strictAllowed.contains a)

/-- Result of a successful strict audit. -/
structure StrictReport where
  decl : Name
  /-- the reachable axiom closure (sorted); all of it is in `strictAllowed` -/
  axioms : Array Name
  deriving Inhabited

/-- Raw reachable closure of an existing constant (no judgement). -/
def rawAxioms (decl : Name) : CoreM (Array Name) := do
  unless (← getEnv).contains decl do
    throwError "#ved_strict_audit: unknown declaration {decl}"
  return sortNames (← collectAxioms decl)

/-- The strict audit.  Throws, naming every offending axiom, unless `decl`
exists, is a theorem, has no metavariables, and its reachable axiom closure
is a subset of `strictAllowed`. -/
def strictAudit (decl : Name) : CoreM StrictReport := do
  let env ← getEnv
  let some ci := env.find? decl
    | throwError "#ved_strict_audit: unknown declaration {decl}"
  let kind : Option String := match ci with
    | .thmInfo _ => none
    | .defnInfo _ => some "a def"
    | .axiomInfo _ => some "an axiom"
    | .opaqueInfo _ => some "an opaque constant"
    | .quotInfo _ => some "a quotient primitive"
    | .inductInfo _ => some "an inductive type"
    | .ctorInfo _ => some "a constructor"
    | .recInfo _ => some "a recursor"
  if let some k := kind then
    throwError "#ved_strict_audit: {decl} is {k}, not a theorem"
  let some value := ci.value? (allowOpaque := true)
    | throwError "#ved_strict_audit: {decl} has no proof term"
  if ci.type.hasMVar || value.hasMVar then
    throwError "#ved_strict_audit: {decl} contains metavariables"
  let axs := sortNames (← collectAxioms decl)
  let off := offendingOf axs
  unless off.isEmpty do
    let sorryNote := if off.contains ``sorryAx then " (depends on sorry)" else ""
    throwError "#ved_strict_audit: {decl} REJECTED{sorryNote}: non-standard axioms {showNames off} (closure {showNames axs})"
  return { decl, axioms := axs }

private def resolveDecl (id : Ident) : CommandElabM Name := do
  try
    liftCoreM <| realizeGlobalConstNoOverload id
  catch _ =>
    throwError "#ved_strict_audit: unknown declaration {id.getId}"

/-- `#ved_strict_audit d`: error naming every offending axiom, otherwise
`VED STRICT OK d: [axioms]`. -/
elab "#ved_strict_audit " id:ident : command => do
  let decl ← resolveDecl id
  let r ← liftCoreM <| strictAudit decl
  logInfo m!"VED STRICT OK {r.decl}: {showNames r.axioms}"

/-- `#ved_axioms_raw d`: MEASUREMENT ONLY (U0).  Prints the raw reachable
closure; it accepts nothing. -/
elab "#ved_axioms_raw " id:ident : command => do
  let decl ← resolveDecl id
  let axs ← liftCoreM <| rawAxioms decl
  logInfo m!"VED AXIOMS RAW {decl}: {showNames axs}"

/-- Shared by `#ved_audit_generated` and `#ved_audit_current_namespace`:
enumerate the theorems declared in this file strictly under `pfx` and print
one `VED AUDIT` line each.  MEASUREMENT ONLY (see the module docstring for
what it does not audit). -/
def auditUnder (pfx : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut found : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if let .thmInfo _ := ci then
      if pfx.isPrefixOf n && n != pfx then found := found.push n
  found := sortNames found
  if found.isEmpty then
    logInfo m!"VED AUDIT none: no theorem declared under {pfx}"
  for n in found do
    let axs ← liftCoreM <| rawAxioms n
    let verdict ← liftCoreM do
      try
        let _ ← strictAudit n
        pure "OK"
      catch _ => pure "REJECTED"
    logInfo m!"VED AUDIT {n} strict={verdict} axioms={showNames axs}"

/-- `#ved_audit_generated Ns`: MEASUREMENT ONLY (U0).  For every theorem
DECLARED IN THE CURRENT FILE under the namespace `Ns`, print one line
`VED AUDIT <decl> strict=OK|REJECTED axioms=[raw closure]`.  The namespace
only FINDS the declarations; the verdict is `strictAudit` (closure ⊆
`strictAllowed`).  It never throws on a rejected theorem, so a case can record
every produced theorem; it accepts nothing by itself.  It does NOT check that
all expected theorems exist, nor any theorem's statement (module docstring). -/
elab "#ved_audit_generated " ns:ident : command => auditUnder ns.getId

/-- `#ved_audit_current_namespace`: `#ved_audit_generated` for the CURRENT
namespace (the U0 in-file cases run `#verify_elab_deep` inside a fresh
namespace nested in the file's own, whose full name the case file does not
spell out).  Same limits as `#ved_audit_generated`. -/
elab "#ved_audit_current_namespace" : command => do
  auditUnder (← getCurrNamespace)

end Tools.VedStrictAudit
