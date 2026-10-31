import Tools.ShippingGen5NameKids7
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
-- NOT BUILT. U7 check: TYPE 1 / MUTANT 4 (single-point; signature/defeq rejection, not semantic counterexamples; no block mutant) / use-site 1 / closure negatives 8 + clean 1 / REACH 1 / AXIOMS 1 (standard three only).
-- Count rule: one `logInfo` line per class: TYPE = theorem vs its Expected; MUTANT = distinct mutant def counted once (MutNoHg, MutHgTrue, MutConclSpans, MutSNone); REACH/AXIOMS = one per theorem.
-- `hg` is a premise; no instance of it is constructed (not evidence of non-vacuity). No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U7 checks

`ExpReachClosedOrdPathF` is written from the Lean text of freeze `BOUNDARY_AUDIT_FREEZE_U7.md` §2, with the defs `GraphAgrees` / `ReachClosed` of Kids3 (the reducible comparator does not unfold them), not from the implementation.
ONE comparator (`cmpTeleR` / `checkExpectedR` / `checkMutantR` of `Tests.Gen5.NameKidsCheck`) is used for the positive and the mutants.
Mutants are well-typed single-point variants; a rejection is by signature / defeq, NOT a semantic counterexample. -/

namespace Tests.Gen5.NameKids7Check
open Lean Meta
open Sparkle.Compiler.Elab (MachineShape)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSrm7Rank (CallGraph callees InClass)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachClosed ReachSpans OrdPath hself_all_reached)
open Tools.ShippingGen5NameKids7
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected statement (from freeze §2 text) -/
def ExpReachClosedOrdPathF : Prop := ∀ {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (OrdPath g top) S), ReachClosed (OrdPath g top) S

/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutNoHg : Prop := ∀ {g : CallGraph} {top : Name} {S : Name → Option MachineShape},
    ReachClosed (OrdPath g top) S
def MutHgTrue : Prop := ∀ {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (fun _ => True) S), ReachClosed (OrdPath g top) S
def MutConclSpans : Prop := ∀ {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (OrdPath g top) S), ReachSpans g top (OrdPath g top)
def MutSNone : Prop := ∀ {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (OrdPath g top) (fun _ => none)), ReachClosed (OrdPath g top) (fun _ => none)

/-! ## 3. Use site (type check, not a semantic claim): closure conclusion kept explicitly next to the U3 consumer output.
No consumer takes `ReachClosed`; this only states that both facts are available for the same set under `hg`. -/
example {g : CallGraph} {B r : Nat} {top : Name} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g (OrdPath g top) S) :
    ReachClosed (OrdPath g top) S ∧ ReachSpans g top (OrdPath g top) ∧
    (∀ c, OrdPath g top c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c) :=
  ⟨reachClosed_ordPath hg, fun _ h => h, hself_all_reached (r := r) hin hg (fun _ h => h)⟩

/-! ## 4. Theorem positive and mutants (same reducible comparator) -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``reachClosed_ordPath ``ExpReachClosedOrdPathF
  checkMutantR ``reachClosed_ordPath ``MutNoHg
  checkMutantR ``reachClosed_ordPath ``MutHgTrue
  checkMutantR ``reachClosed_ordPath ``MutConclSpans
  checkMutantR ``reachClosed_ordPath ``MutSNone

/-! ## 5. Closure audit (U1/U2 walker: root-self judgement, unknown name fails, type-only path asserted) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK7 AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK7 AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK7 AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK7 AUDIT FAILED: {what} accepted"
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
  logInfo m!"NK7 CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``reachClosed_ordPath] do
    let a ← auditRoot env.find? r
    logInfo m!"NK7 REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``reachClosed_ordPath] do
    checkAxioms n

end Tests.Gen5.NameKids7Check
