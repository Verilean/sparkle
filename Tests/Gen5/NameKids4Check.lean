import Tools.ShippingGen5NameKids4
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
-- NOT BUILT (no build of this tree yet; the Pod build SHA is recorded by a later comment-only commit). Written against freeze BOUNDARY_AUDIT_FREEZE_U4.md §3.
-- Count rule: each count is the number of `logInfo` lines of one class (TYPE = theorem compared against its Expected; MUTANT = distinct mutant def or cross-statement control, each counted once; REACH/AXIOMS = one per theorem).
-- hF is an existence premise, not the production bridge. No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U4 checks

Every `Exp…` statement is written from the Lean text of freeze `BOUNDARY_AUDIT_FREEZE_U4.md` §2, not from the implementation.
ONE comparator (`cmpTeleR` / `checkExpectedR` / `checkMutantR` of `Tests.Gen5.NameKidsCheck`) is used for positives and mutants.
Mutants are single-point, well-typed variants; a rejection is by signature / defeq, NOT a semantic counterexample. -/

namespace Tests.Gen5.NameKids4Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel (machineShapeF)
open Tools.ShippingGen5NameKids2 (MemTagsNamed)
open Tools.ShippingGen5NameKids4
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected statements (from freeze §2 text) -/
def ExpMemTagsF : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)), MemTagsNamed sp
def ExpHmemF : Prop := ∀ {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)),
    ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp

/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutMemTagsNone : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some none), MemTagsNamed sp
def MutMemTagsNeg : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)), ¬ MemTagsNamed sp
def MutHmemNoReach : Prop := ∀ {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)),
    ∀ c, ∀ sp, S c = some sp → MemTagsNamed sp
def MutHmemNone : Prop := ∀ {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)),
    ∀ c, Reach c → ∀ sp, S c = none → MemTagsNamed sp
def MutHmemAll : Prop := ∀ {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∀ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)),
    ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp

/-! ## 3. Use site (type check, not a semantic claim): the output has the type of the `hmem` binder of U3 -/
section Use
open Tools.ShippingSrm7Rank (CallGraph InClass)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans sepK_parent_all_reached)
example {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach)
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)) :=
  sepK_parent_all_reached hin hg hsp (hmem_of_machineShapeF hF)
end Use

/-! ## 4. Theorem positives and mutants (same reducible comparator) -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``memTagsNamed_of_machineShapeF ``ExpMemTagsF
  checkExpectedR ``hmem_of_machineShapeF ``ExpHmemF
  checkMutantR ``memTagsNamed_of_machineShapeF ``MutMemTagsNone
  checkMutantR ``memTagsNamed_of_machineShapeF ``MutMemTagsNeg
  checkMutantR ``hmem_of_machineShapeF ``MutHmemNoReach
  checkMutantR ``hmem_of_machineShapeF ``MutHmemNone
  checkMutantR ``hmem_of_machineShapeF ``MutHmemAll
  -- cross-statement controls
  checkMutantR ``memTagsNamed_of_machineShapeF ``ExpHmemF
  checkMutantR ``hmem_of_machineShapeF ``ExpMemTagsF

/-! ## 5. Closure audit (U1/U2 walker: root-self judgement, unknown name fails, type-only path asserted) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK4 AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK4 AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK4 AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK4 AUDIT FAILED: {what} accepted"
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
  logInfo m!"NK4 CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``memTagsNamed_of_machineShapeF, ``hmem_of_machineShapeF] do
    let a ← auditRoot env.find? r
    logInfo m!"NK4 REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``memTagsNamed_of_machineShapeF, ``hmem_of_machineShapeF] do
    checkAxioms n

end Tests.Gen5.NameKids4Check
