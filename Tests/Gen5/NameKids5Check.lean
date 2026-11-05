import Tools.ShippingGen5NameKids5
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
-- Reviewed build: ba11v-76ae2e8e (exit 0, 724 jobs, approved at 76ae2e8e; src=base=end, dirty=false). U5 check: TYPE 1 / MUTANT 4 (single-point, signature/defeq rejection, not semantic counterexamples) / closure negatives 8 + clean 1 / REACH 1 / AXIOMS 1 ([propext, Quot.sound], a subset of the standard three).
-- Count rule: each count is the number of `logInfo` lines of one class (TYPE = theorem compared against its Expected; MUTANT = distinct mutant def, each counted once; REACH/AXIOMS = one per theorem). MUTANT 4 = single-point variants 4 (MutNoReach, MutSNone, MutForall, MutReverse); no block mutant, no cross-statement control.
-- hfo is a sufficient condition, not equivalent to GraphAgrees, and not supplied. No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U5 checks

`ExpGraphAgreesF` is written from the Lean text of freeze `BOUNDARY_AUDIT_FREEZE_U5.md` §2, not from the implementation.
ONE comparator (`cmpTeleR` / `checkExpectedR` / `checkMutantR` of `Tests.Gen5.NameKidsCheck`) is used for the positive and the mutants.
Mutants are well-typed single-point variants; a rejection is by signature / defeq, NOT a semantic counterexample. -/

namespace Tests.Gen5.NameKids5Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm15Graph (graphOf FirstOcc)
open Tools.ShippingGen5NameKids3 (GraphAgrees)
open Tools.ShippingGen5NameKids5
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected statement (from freeze §2 text) -/
def ExpGraphAgreesF : Prop := ∀ {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape),
    GraphAgrees (graphOf ds) Reach S

/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutNoReach : Prop := ∀ {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hfo : ∀ c, ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape),
    GraphAgrees (graphOf ds) Reach S
def MutSNone : Prop := ∀ {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = none),
    GraphAgrees (graphOf ds) Reach S
def MutForall : Prop := ∀ {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hfo : ∀ c, Reach c → ∀ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape),
    GraphAgrees (graphOf ds) Reach S
def MutReverse : Prop := ∀ {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape),
    GraphAgrees (graphOf ds.reverse) Reach S

/-! ## 3. Use site (type check, not a semantic claim): the output has the type of the `hg` binder of U3 -/
section Use
open Tools.ShippingSrm7Rank (InClass)
open Tools.ShippingGen5NameKids2 (MemTagsNamed)
open Tools.ShippingGen5NameKids3 (ReachSpans sepK_parent_all_reached)
example {ds : List (Name × MachineData)} {B : Nat} {top : Name} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hin : InClass (graphOf ds) B top = true) (hsp : ReachSpans (graphOf ds) top Reach)
    (hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape)
    (hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp) :=
  sepK_parent_all_reached hin (graphAgrees_of_firstOcc hfo) hsp hmem
end Use

/-! ## 4. Theorem positive and mutants (same reducible comparator) -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``graphAgrees_of_firstOcc ``ExpGraphAgreesF
  checkMutantR ``graphAgrees_of_firstOcc ``MutNoReach
  checkMutantR ``graphAgrees_of_firstOcc ``MutSNone
  checkMutantR ``graphAgrees_of_firstOcc ``MutForall
  checkMutantR ``graphAgrees_of_firstOcc ``MutReverse

/-! ## 5. Closure audit (U1/U2 walker: root-self judgement, unknown name fails, type-only path asserted) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK5 AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK5 AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK5 AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK5 AUDIT FAILED: {what} accepted"
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
  logInfo m!"NK5 CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``graphAgrees_of_firstOcc] do
    let a ← auditRoot env.find? r
    logInfo m!"NK5 REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``graphAgrees_of_firstOcc] do
    checkAxioms n

end Tests.Gen5.NameKids5Check
