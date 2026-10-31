import Tools.ShippingGen5NameKids6
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
-- Reviewed build ba13v-b07cfcec (approved at b07cfcec): exit 0, 724 jobs. U6 check: TYPE 1 / MUTANT 4 (single-point; signature/defeq rejection, not semantic counterexamples; no block mutant) / use-site 1 / closure negatives 8 + clean 1 / REACH 1 / AXIOMS 1 (standard three only).
-- Count rule: one `logInfo` line per class: TYPE = theorem vs its Expected; MUTANT = distinct mutant def counted once (MutNoHnd, MutNoHr, MutNeq, MutReverse); REACH/AXIOMS = one per theorem.
-- hnd / hr are premises, not supplied for the production program. No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U6 checks

`ExpInClassGraphOfF` is written from the Lean text of freeze `BOUNDARY_AUDIT_FREEZE_U6.md` §2, not from the implementation.
ONE comparator (`cmpTeleR` / `checkExpectedR` / `checkMutantR` of `Tests.Gen5.NameKidsCheck`) is used for the positive and the mutants.
Mutants are well-typed single-point variants; a rejection is by signature / defeq, NOT a semantic counterexample. -/

namespace Tests.Gen5.NameKids6Check
open Lean Meta
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm15Graph (graphOf)
open Tools.ShippingSrm7Rank (InClass declRank)
open Tools.ShippingGen5NameKids6
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected statement (from freeze §2 text) -/
def ExpInClassGraphOfF : Prop := ∀ {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true),
    InClass (graphOf ds) B top = true

/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutNoHnd : Prop := ∀ {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hr : (declRank (graphOf ds) B top).isSome = true),
    InClass (graphOf ds) B top = true
def MutNoHr : Prop := ∀ {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length),
    InClass (graphOf ds) B top = true
def MutNeq : Prop := ∀ {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length ≠ ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true),
    InClass (graphOf ds) B top = true
def MutReverse : Prop := ∀ {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true),
    InClass (graphOf ds.reverse) B top = true

/-! ## 3. Use site (type check, not a semantic claim): the output has the type of the `hin` binder of U3 -/
section Use
open Sparkle.Compiler.Elab
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans hself_all_reached)
example {ds : List (Name × MachineData)} {B : Nat} {top : Name} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true)
    (hg : GraphAgrees (graphOf ds) Reach S) (hsp : ReachSpans (graphOf ds) top Reach) :=
  hself_all_reached (r := 0) (inClass_graphOf hnd hr) hg hsp
end Use

/-! ## 4. Theorem positive and mutants (same reducible comparator) -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``inClass_graphOf ``ExpInClassGraphOfF
  checkMutantR ``inClass_graphOf ``MutNoHnd
  checkMutantR ``inClass_graphOf ``MutNoHr
  checkMutantR ``inClass_graphOf ``MutNeq
  checkMutantR ``inClass_graphOf ``MutReverse

/-! ## 5. Closure audit (U1/U2 walker: root-self judgement, unknown name fails, type-only path asserted) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK6 AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK6 AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK6 AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK6 AUDIT FAILED: {what} accepted"
  expectHit "edge root->forbidden" env.find? (F ++ `badRoot) [F ++ `badRoot, ``Lean.ofReduceBool]
  expectHit "helper value" env.find? (F ++ `badViaValue) [F ++ `badViaValue, F ++ `helperV, ``Lean.ofReduceBool]
  let asAxiom := fun (ci : ConstantInfo) => ConstantInfo.axiomInfo { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false }
  let synthRoot := fun (root helper : Name) =>
    ConstantInfo.thmInfo { name := root, levelParams := [], type := mkConst ``True, value := mkConst helper, all := [root] }
  let SR := F ++ `synthRoot
  let tyOnly := fun n =>
    if n == SR then some (synthRoot SR (F ++ `helperTy))
    else if n == F ++ `helperTy then (env.find? n).map asAxiom
    else env.find? n
  expectHit "helper type" tyOnly SR [SR, F ++ `helperTy, ``Lean.ofReduceBool]
  expectHit "forbidden root ofReduceBool" env.find? ``Lean.ofReduceBool [``Lean.ofReduceBool]
  expectHit "forbidden root sorryAx" env.find? ``sorryAx [``sorryAx]
  expectUnknown "unknown root" (fun n => if n == F ++ `badRoot then none else env.find? n) (F ++ `badRoot) [F ++ `badRoot]
  expectUnknown "unknown helper value" (fun n => if n == F ++ `helperV then none else env.find? n) (F ++ `badViaValue) [F ++ `badViaValue, F ++ `helperV]
  let tyOnlyU := fun n =>
    if n == SR then some (synthRoot SR (F ++ `helperTyU))
    else if n == F ++ `auxT then none
    else if n == F ++ `helperTyU then (env.find? n).map asAxiom
    else env.find? n
  expectUnknown "unknown name via helper type" tyOnlyU SR [SR, F ++ `helperTyU, F ++ `auxT]
  let rc ← auditRoot env.find? (F ++ `cleanRoot)
  logInfo m!"NK6 CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``inClass_graphOf] do
    let a ← auditRoot env.find? r
    logInfo m!"NK6 REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``inClass_graphOf] do
    checkAxioms n

end Tests.Gen5.NameKids6Check
