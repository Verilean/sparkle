import Lean
import Tools.ShippingGen4ParamBridgeLegal
set_option autoImplicit false
-- NOT BUILT: Check of Tools/ShippingGen4ParamBridgeLegal.lean (scripts/gen4/PARAMETRIC_BRIDGE_UNIT6_FREEZE.md §3). Silent on success. Mutants are rejections by signature/defeq/proof failure, not semantic counterexamples.
-- Directive counts (rule: top-level `#...` lines per kind): proves 3 (incl. 1 positive control), not_proves 5 (def mutants of requirePositiveM: 4 single + 1 compound), type_defeq 5, mutant_rejected 7 (theorem mutants), audit_axioms 7, audit_closure 6, closure_detects 2, closure_clean 2, sig_clean 2, closure_unknown_fixtures 1. No sorry, no native_decide. Opaque bodies are type-only in the closure.

open Lean Elab Command Meta

/-- The single comparator used by every TYPE/VALUE check and every MUTANT check. -/
def defeqTo (a b : Expr) : MetaM Bool := withReducible (isDefEq a b)

elab "#type_defeq " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  unless ← defeqTo info.type ty do throwError "TYPE mismatch for {n}"

elab "#mutant_rejected " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  if ← defeqTo info.type ty then throwError "mutant NOT rejected for {n}"

elab "#audit_axioms " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let axs ← collectAxioms n
  let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless bad.isEmpty do throwError "{n}: axioms {bad}"

/-- Transitive constant closure. The body is fetched explicitly per `ConstantInfo` kind:
`thmInfo.value` and `defnInfo.value` are traversed; `opaqueInfo` bodies are NOT tracked (only the type is), and the
opaque constants reached are returned so the log can state it. Other kinds (axiom, inductive, ctor, rec, quot) have
no body, only a type. A name that `env.find?` does not resolve is NOT skipped: it is collected in the third component
and the production audit fails on it. Returns (seen, opaque constants reached, unresolved names). -/
private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) (opq : NameSet) (unk : NameSet) :
    NameSet × NameSet × NameSet :=
  match todo with
  | [] => (seen, opq, unk)
  | n :: rest =>
    if seen.contains n then closure env rest seen opq unk else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen opq (unk.insert n)
    | some ci =>
      let (body, opq) : List Name × NameSet := match ci with
        | .thmInfo v => (v.value.getUsedConstants.toList, opq)
        | .defnInfo v => (v.value.getUsedConstants.toList, opq)
        | .opaqueInfo _ => ([], opq.insert n)
        | _ => ([], opq)
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen opq unk

/-- The one detector, used by production checks and by the fixtures (also on synthetic environments).
Returns (forbidden constants reached, opaque constants reached, unresolved names). -/
private def closureReportIn (env : Environment) (forbidden : List Name) (n : Name) :
    List Name × List Name × List Name :=
  let (seen, opq, unk) := closure env [n] {} {} {}
  (seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m, opq.toList, unk.toList)

private def closureReport (forbidden : List Name) (n : Name) : CoreM (List Name × List Name × List Name) := do
  return closureReportIn (← getEnv) forbidden n

private def prodForbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamBridgeLegalCheck.Fixture.Bad]

elab "#audit_closure " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let (bad, opq, unk) ← closureReport prodForbidden n
  unless unk.isEmpty do throwError "{n}: closure reached names not found in the environment: {unk}"
  unless opq.isEmpty do logInfo m!"CLOSURE {n}: opaque bodies NOT tracked (type only): {opq}"
  unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"

/-- Fixture must be flagged by the same detector (fixture-only forbidden name). -/
elab "#closure_detects " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let (bad, _, _) ← closureReport fixtureForbidden n
  if bad.isEmpty then throwError "{n}: detector MISSED the forbidden constant"

/-- Fixture must not be flagged by the same detector. -/
elab "#closure_clean " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let (bad, _, _) ← closureReport fixtureForbidden n
  unless bad.isEmpty do throwError "{n}: detector flagged a clean fixture: {bad}"

/-- Unresolved-name fixtures, through the same `closureReport` as `#audit_closure`. Synthetic declarations are added
with the kernel check skipped (`debug.skipKernelTC`; the kernel would refuse an unknown constant) inside
`withoutModifyingEnv`, so they never reach the file's environment. Three negatives (unknown root, unknown name reached
through a helper VALUE, through a helper TYPE) must report the unknown name; the clean control (same shapes, all names
known) must report none. -/
elab "#closure_unknown_fixtures" : command => liftTermElabM do
  let nat := Expr.const ``Nat []
  let zero := Expr.const ``Nat.zero []
  let add (nm : Name) (ty val : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.defnDecl { name := nm, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })
  -- negative 1: the root itself does not exist
  withoutModifyingEnv do
    let (_, _, unk) ← closureReport fixtureForbidden `Fixture.Unknown.root
    unless unk.contains `Fixture.Unknown.root do throwError "unknown ROOT was not reported"
  -- negative 2: helper VALUE mentions an unknown constant
  withoutModifyingEnv do
    add `Fixture.Unknown.hv nat (.const `Fixture.Unknown.v [])
    add `Fixture.Unknown.rootV nat (.const `Fixture.Unknown.hv [])
    let (_, _, unk) ← closureReport fixtureForbidden `Fixture.Unknown.rootV
    unless unk.contains `Fixture.Unknown.v do throwError "unknown name via helper VALUE was not reported: {unk}"
  -- negative 3: helper TYPE mentions an unknown constant
  withoutModifyingEnv do
    add `Fixture.Unknown.hT (.const `Fixture.Unknown.T []) zero
    add `Fixture.Unknown.rootT nat (.const `Fixture.Unknown.hT [])
    let (_, _, unk) ← closureReport fixtureForbidden `Fixture.Unknown.rootT
    unless unk.contains `Fixture.Unknown.T do throwError "unknown name via helper TYPE was not reported: {unk}"
  -- clean control: same shapes, everything resolves
  withoutModifyingEnv do
    add `Fixture.Unknown.cv nat zero
    add `Fixture.Unknown.cT nat zero
    add `Fixture.Unknown.cRoot nat (.const `Fixture.Unknown.cv [])
    add `Fixture.Unknown.cRoot2 (.const `Fixture.Unknown.cT []) zero
    let (_, _, unk) ← closureReport fixtureForbidden `Fixture.Unknown.cRoot
    let (_, _, unk2) ← closureReport fixtureForbidden `Fixture.Unknown.cRoot2
    unless unk.isEmpty && unk2.isEmpty do throwError "clean control reported unresolved names: {unk} {unk2}"

/-- The fixture's signature must not itself mention the forbidden name (only the proof may). -/
elab "#sig_clean " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let ci ← getConstInfo n
  if ci.type.getUsedConstants.any (fixtureForbidden.contains ·) then throwError "{n}: signature mentions forbidden name"

/-- Run `tac` on the goal `t`. Tactic errors are recovered (logged, goal admitted) by the elaborator, so the message log is
captured: the run is OK only if no error was logged, no goal remains and the proof term has no `sorry`. The captured
messages are returned (and not left in the log). -/
private def runProof (t : Syntax) (tac : Syntax) : TermElabM (Bool × MessageLog) := do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let saved ← Core.getAndEmptyMessageLog
  let mv ← mkFreshExprMVar ty
  let ok ← try
      let gs ← Term.withoutErrToSorry (Tactic.run mv.mvarId! (Tactic.evalTactic tac))
      let v ← instantiateMVars mv
      pure (gs.isEmpty && !v.hasSorry)
    catch _ => pure false
  let msgs ← Core.getAndEmptyMessageLog
  Core.setMessageLog saved
  return (ok && !msgs.hasErrors, msgs)

/-- Positive: the statement must be proved by the given tactic script (no error, no sorry, no remaining goals). -/
elab "#proves " t:term " := " tac:tacticSeq : command => liftTermElabM do
  let (ok, msgs) ← runProof t tac
  unless ok do
    for m in msgs.toList do logMessage m
    throwError "#proves: statement not proved"

/-- Mutant: the SAME statement shape and tactic script must FAIL (error, unsolved goals or sorry). -/
elab "#not_proves " t:term " := " tac:tacticSeq : command => liftTermElabM do
  let (ok, _) ← runProof t tac
  if ok then throwError "mutant NOT rejected: the agreement/clause proof succeeded"

namespace Tests.Gen4.ParamBridgeLegalCheck
open Sparkle.IR.AST Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeSpecType
  Tools.ShippingGen4ParamBridgeLegal

abbrev Th := List (String × Nat)

/-! ## 0. Independent Expected (from Specialize.lean:42-44 text; not opening the Tool's model) -/
def ExpReq (context : String) (value : Nat) : Except String Nat :=
  if value == 0 then .error s!"{context} specializes to zero width" else .ok value

/-- necessary conditions only (NOT equivalent to LegalBinding: duplicates / unknown names / declaration duplicates are not covered) -/
def ExpLegal (D : Design) (θ : Th) : Prop :=
  (∀ p ∈ θ, p.2 ≠ 0) ∧ ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v

/-- agreement of the F1 model with the independent text, all arguments -/
theorem agree_req : ∀ (c : String) (v : Nat), requirePositiveM c v = ExpReq c v := by
  intro c v; rfl

/-- the two theorems together give exactly the necessary conditions -/
theorem legal_necessary {D : Design} {θ : Th} (h : LegalBinding D θ) : ExpLegal D θ :=
  ⟨fun p hp => Nat.pos_iff_ne_zero.mp (legalBinding_allPos h p hp), legalBinding_covers h⟩

/-! ## 1. Clause statements (def mutants of requirePositiveM, same tactic) -/
#proves ∀ (c : String) (v : Nat), requirePositiveM c v = ExpReq c v := intro c v; rfl
#proves ∀ (c : String) (v : Nat), specRequirePositive c v = ExpReq c v := intro c v; rw [requirePositive_eq]; rfl
-- def mutants of requirePositiveM written as local copies and compared to ExpReq (single)
def MReqNe (c : String) (v : Nat) : Except String Nat :=
  if v != 0 then .error s!"{c} specializes to zero width" else .ok v
def MReqOne (c : String) (v : Nat) : Except String Nat :=
  if v == 1 then .error s!"{c} specializes to zero width" else .ok v
def MReqMsg (c : String) (v : Nat) : Except String Nat :=
  if v == 0 then .error s!"{c} zero" else .ok v
def MReqOk0 (c : String) (v : Nat) : Except String Nat :=
  if v == 0 then .error s!"{c} specializes to zero width" else .ok 0
def MReqBoth (c : String) (v : Nat) : Except String Nat :=
  if v != 0 then .error s!"{c} zero" else .ok v
#not_proves ∀ (c : String) (v : Nat), MReqNe c v = ExpReq c v := intro c v; unfold MReqNe ExpReq; rcases hv : (v == 0) <;> simp_all
#not_proves ∀ (c : String) (v : Nat), MReqOne c v = ExpReq c v := intro c v; unfold MReqOne ExpReq; rcases hv : (v == 0) <;> simp_all
#not_proves ∀ (c : String) (v : Nat), MReqMsg c v = ExpReq c v := intro c v; unfold MReqMsg ExpReq; rcases hv : (v == 0) <;> simp_all
#not_proves ∀ (c : String) (v : Nat), MReqOk0 c v = ExpReq c v := intro c v; unfold MReqOk0 ExpReq; rcases hv : (v == 0) <;> simp_all
#not_proves ∀ (c : String) (v : Nat), MReqBoth c v = ExpReq c v := intro c v; unfold MReqBoth ExpReq; rcases hv : (v == 0) <;> simp_all
-- positive control for the same script shape
#proves ∀ (c : String) (v : Nat), requirePositiveM c v = ExpReq c v := intro c v; unfold requirePositiveM ExpReq; rcases hv : (v == 0) <;> simp_all

/-! ## 2. Theorem types (complete types of the freeze, independent copies) -/
#type_defeq requirePositive_eq : ∀ (context : String) (value : Nat), specRequirePositive context value = requirePositiveM context value
#type_defeq legalBinding_allPos : ∀ {D : Design} {θ : Th}, LegalBinding D θ → AllPos θ
#type_defeq legalBinding_covers : ∀ {D : Design} {θ : Th}, LegalBinding D θ →
    ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v
#type_defeq agree_req : ∀ (c : String) (v : Nat), requirePositiveM c v = ExpReq c v
#type_defeq legal_necessary : ∀ {D : Design} {θ : Th}, LegalBinding D θ → ExpLegal D θ

/-! ## 3. Theorem mutants (well-typed; rejected by signature/defeq) -/
#mutant_rejected legalBinding_allPos : ∀ {D : Design} {θ : Th}, LegalBinding D θ → ∀ p ∈ θ, p.2 < 5
#mutant_rejected legalBinding_allPos : ∀ {D : Design} {θ : Th}, LegalBinding D θ → AllPos (θ.reverse.tail)
#mutant_rejected legalBinding_allPos : ∀ {D : Design} {θ : Th}, AllPos θ
#mutant_rejected legalBinding_covers : ∀ {D : Design} {θ : Th}, LegalBinding D θ →
    ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∀ v, θ.lookup q.name = some v
#mutant_rejected legalBinding_covers : ∀ {D : Design} {θ : Th}, LegalBinding D θ →
    ∀ m ∈ D.modules, ∀ q ∈ m.parameters, θ.lookup q.name = none
#mutant_rejected requirePositive_eq : ∀ (context : String) (value : Nat), specRequirePositive context value = .ok value
#mutant_rejected requirePositive_eq : ∀ (context : String) (value : Nat), specRequirePositive context value = ExpReq context 0

/-! ## 4. AXIOMS and CLOSURE -/
#audit_axioms requirePositive_eq
#audit_axioms legalBinding_allPos
#audit_axioms legalBinding_covers
#audit_axioms legal_facts
#audit_axioms forIn_yield_each
#audit_axioms agree_req
#audit_axioms legal_necessary
#audit_closure requirePositive_eq
#audit_closure legalBinding_allPos
#audit_closure legalBinding_covers
#audit_closure legal_facts
#audit_closure forIn_yield_each
#audit_closure legal_necessary

/-! ## 7. CLOSURE detector fixtures (same detector, fixture-only forbidden name; unknown names fail) -/
namespace Fixture
def Bad : Nat := 0
theorem negDirect : True := by
  have _h : Bad = Bad := rfl
  exact True.intro
theorem posOk : True := by
  have _h : (0 : Nat) = 0 := rfl
  exact True.intro
end Fixture
namespace FixtureHelper
theorem helperBad : True := by
  have _h : Fixture.Bad = Fixture.Bad := rfl
  exact True.intro
theorem helperOk : True := by
  have _h : (1 : Nat) = 1 := rfl
  exact True.intro
end FixtureHelper
theorem negViaHelper : True := FixtureHelper.helperBad
theorem posViaHelper : True := FixtureHelper.helperOk
#sig_clean Fixture.negDirect
#sig_clean negViaHelper
#closure_detects Fixture.negDirect
#closure_detects negViaHelper
#closure_clean Fixture.posOk
#closure_clean posViaHelper
#closure_unknown_fixtures

end Tests.Gen4.ParamBridgeLegalCheck
