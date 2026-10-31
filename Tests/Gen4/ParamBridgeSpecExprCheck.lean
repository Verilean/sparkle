import Lean
import Tools.ShippingGen4ParamBridgeSpecExpr
set_option autoImplicit false
-- NOT BUILT: Check of Tools/ShippingGen4ParamBridgeSpecExpr.lean (scripts/gen4/PARAMETRIC_BRIDGE_UNIT5_FREEZE.md §3). Directive counts, measured (rule: top-level `#...` directive lines per kind, silent on success):
-- proves 27 (clause statements: specExprM 7 + specExprsM 2 + ExprOK 7 + ExprsOK 2 + NoDim 7 + NoDims 2; one of them multi-line), not_proves 12 (def mutants:
-- 6 slice-clause, 2 list-clause, 1 index-clause, 2 ExprOK, 1 NoDim), type_defeq 9, mutant_rejected 9 (theorem mutants), audit_axioms 9, audit_closure 9,
-- closure_detects 2, closure_clean 2, sig_clean 2, closure_unknown_fixtures 1. Agreement theorems: 6 (agree_spec/specs/ok/oks/noDim/noDims; mutual).
-- Def mutants are checked at CLAUSE level (the recursive call is a parameter, compared with the independent clause body XSliceDim/XList/XIndex or the
-- independent ExprOK/NoDim clause statement), not by a mutual agreement theorem on a whole mutated mutual definition. No sorry, no native_decide.
-- Closure limitation: opaque bodies (DimExpr.evaluate, specializeType, specializeExpr) are NOT followed by the
-- `getUsedConstants`-based closure; only their types are. Opaque constants reached are logged.

/-! # Check of Tools/ShippingGen4ParamBridgeSpecExpr.lean against scripts/gen4/PARAMETRIC_BRIDGE_UNIT5_FREEZE.md §3

Expected definitions `ExpSpec/ExpSpecs/ExpOK/ExpOKs/ExpNoDim/ExpNoDims` are written here from freeze §2/§3 text (explicit `match`, no
reference to the implementation constants). The implementation definitions are compared to them by full-argument
agreement theorems and by per-clause statements (`#proves`); every def mutant (a well-typed single change, defined in this
file) is run through the SAME tactic script on the SAME statement shape (`#not_proves`) and must fail. A mutant rejection is a
failure of the agreement/clause proof or a signature/defeq mismatch, NOT a semantic counterexample. -/

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

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamBridgeSpecExprCheck.Fixture.Bad]

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

namespace Tests.Gen4.ParamBridgeSpecExprCheck
open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape Tools.ShippingGen4ParamBridgeCompose
  Tools.ShippingGen4ParamBridgeSpecExpr

abbrev SE := Sparkle.IR.AST.Expr
abbrev Th := List (String × Nat)

/-! ## 0. Independent Expected definitions (freeze §2/§3; explicit `match`, no implementation constants) -/
mutual
def ExpSpec (θ : Th) : SE → Except String SE
  | .const v w => .ok (.const v w)
  | .ref n => .ok (.ref n)
  | .op o args =>
      match ExpSpecs θ args with
      | .error m => .error m
      | .ok a => .ok (.op o a)
  | .concat args =>
      match ExpSpecs θ args with
      | .error m => .error m
      | .ok a => .ok (.concat a)
  | .slice e hi lo =>
      match ExpSpec θ e with
      | .error m => .error m
      | .ok a => .ok (.slice a hi lo)
  | .sliceDim e hi lo =>
      match evalM θ hi with
      | .error m => .error m
      | .ok h =>
        match evalM θ lo with
        | .error m => .error m
        | .ok l =>
          if h < l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
          else
            match ExpSpec θ e with
            | .error m => .error m
            | .ok a => .ok (.slice a h l)
  | .index x y =>
      match ExpSpec θ x with
      | .error m => .error m
      | .ok a =>
        match ExpSpec θ y with
        | .error m => .error m
        | .ok b => .ok (.index a b)
def ExpSpecs (θ : Th) : List SE → Except String (List SE)
  | [] => .ok []
  | e :: es =>
      match ExpSpec θ e with
      | .error m => .error m
      | .ok a =>
        match ExpSpecs θ es with
        | .error m => .error m
        | .ok b => .ok (a :: b)
end

mutual
def ExpOK (θ : Th) : SE → Prop
  | .const _ _ => True
  | .ref _ => True
  | .op _ args => ExpOKs θ args
  | .concat args => ExpOKs θ args
  | .slice e _ _ => ExpOK θ e
  | .sliceDim e hi lo => SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ ExpOK θ e
  | .index x y => ExpOK θ x ∧ ExpOK θ y
def ExpOKs (θ : Th) : List SE → Prop
  | [] => True
  | e :: es => ExpOK θ e ∧ ExpOKs θ es
end

mutual
def ExpNoDim : SE → Prop
  | .const _ _ => True
  | .ref _ => True
  | .op _ args => ExpNoDims args
  | .concat args => ExpNoDims args
  | .slice e _ _ => ExpNoDim e
  | .sliceDim .. => False
  | .index x y => ExpNoDim x ∧ ExpNoDim y
def ExpNoDims : List SE → Prop
  | [] => True
  | e :: es => ExpNoDim e ∧ ExpNoDims es
end

/-! ## 1. Full-argument agreement theorems (all arguments quantified, all clauses, both list companions) -/
mutual
theorem agree_spec (θ : Th) : (e : SE) → specExprM θ e = ExpSpec θ e
  | .const v w => by simp [specExprM, ExpSpec]
  | .ref n => by simp [specExprM, ExpSpec]
  | .op o args => by
      have ih := agree_specs θ args
      simp only [specExprM, ExpSpec, ih]
      cases ExpSpecs θ args <;> rfl
  | .concat args => by
      have ih := agree_specs θ args
      simp only [specExprM, ExpSpec, ih]
      cases ExpSpecs θ args <;> rfl
  | .slice e hi lo => by
      have ih := agree_spec θ e
      simp only [specExprM, ExpSpec, ih]
      cases ExpSpec θ e <;> rfl
  | .sliceDim e hi lo => by
      have ih := agree_spec θ e
      simp only [specExprM, ExpSpec, ih]
      cases evalM θ hi with
      | error m => rfl
      | ok h =>
        cases evalM θ lo with
        | error m => rfl
        | ok l =>
          by_cases hlt : h < l
          · simp [hlt, Except.bind]
          · simp only [hlt, if_false, Except.bind]
            cases ExpSpec θ e <;> rfl
  | .index x y => by
      have ih1 := agree_spec θ x
      have ih2 := agree_spec θ y
      simp only [specExprM, ExpSpec, ih1, ih2]
      cases ExpSpec θ x with
      | error m => rfl
      | ok a => cases ExpSpec θ y <;> rfl
theorem agree_specs (θ : Th) : (es : List SE) → specExprsM θ es = ExpSpecs θ es
  | [] => by simp [specExprsM, ExpSpecs]
  | e :: es => by
      have ih1 := agree_spec θ e
      have ih2 := agree_specs θ es
      simp only [specExprsM, ExpSpecs, ih1, ih2]
      cases ExpSpec θ e with
      | error m => rfl
      | ok a => cases ExpSpecs θ es <;> rfl
end

mutual
theorem agree_ok (θ : Th) : (e : SE) → (ExprOK θ e ↔ ExpOK θ e)
  | .const v w => by simp [ExprOK, ExpOK]
  | .ref n => by simp [ExprOK, ExpOK]
  | .op o args => by simp only [ExprOK, ExpOK]; exact agree_oks θ args
  | .concat args => by simp only [ExprOK, ExpOK]; exact agree_oks θ args
  | .slice e hi lo => by simp only [ExprOK, ExpOK]; exact agree_ok θ e
  | .sliceDim e hi lo => by simp only [ExprOK, ExpOK]; rw [agree_ok θ e]
  | .index x y => by simp only [ExprOK, ExpOK]; rw [agree_ok θ x, agree_ok θ y]
theorem agree_oks (θ : Th) : (es : List SE) → (ExprsOK θ es ↔ ExpOKs θ es)
  | [] => by simp [ExprsOK, ExpOKs]
  | e :: es => by simp only [ExprsOK, ExpOKs]; rw [agree_ok θ e, agree_oks θ es]
end

mutual
theorem agree_noDim : (e : SE) → (NoDim e ↔ ExpNoDim e)
  | .const v w => by simp [NoDim, ExpNoDim]
  | .ref n => by simp [NoDim, ExpNoDim]
  | .op o args => by simp only [NoDim, ExpNoDim]; exact agree_noDims args
  | .concat args => by simp only [NoDim, ExpNoDim]; exact agree_noDims args
  | .slice e hi lo => by simp only [NoDim, ExpNoDim]; exact agree_noDim e
  | .sliceDim e hi lo => by simp [NoDim, ExpNoDim]
  | .index x y => by simp only [NoDim, ExpNoDim]; rw [agree_noDim x, agree_noDim y]
theorem agree_noDims : (es : List SE) → (NoDims es ↔ ExpNoDims es)
  | [] => by simp [NoDims, ExpNoDims]
  | e :: es => by simp only [NoDims, ExpNoDims]; rw [agree_noDim e, agree_noDims es]
end

/-! ## 2. Expected clause bodies, parametrised by the recursive call (so a clause mutant is compared on the same shape) -/
def XSliceDim (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  match evalM θ hi with
  | .error m => .error m
  | .ok h =>
    match evalM θ lo with
    | .error m => .error m
    | .ok l =>
      if h < l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
      else
        match rec e with
        | .error m => .error m
        | .ok a => .ok (.slice a h l)
def XList (recs : List SE → Except String (List SE)) (mk : List SE → SE) (args : List SE) : Except String SE :=
  match recs args with
  | .error m => .error m
  | .ok a => .ok (mk a)
def XIndex (rec : SE → Except String SE) (x y : SE) : Except String SE :=
  match rec x with
  | .error m => .error m
  | .ok a =>
    match rec y with
    | .error m => .error m
    | .ok b => .ok (.index a b)

-- the one tactic used by every clause statement (positive) and every clause mutant
macro "sdTac" f:ident : tactic => `(tactic|
  (intro θ rec e hi lo
   simp only [$f:ident, XSliceDim]
   rcases evalM θ hi with m | h <;> rcases evalM θ lo with m2 | l <;> simp [Except.bind] <;>
     (try split) <;> (try (rcases rec e with m3 | a)) <;> simp))
macro "listTac" f:ident : tactic => `(tactic|
  (intro recs mk args
   simp only [$f:ident, XList]
   rcases recs args with m | a <;> simp [Except.bind]))
macro "idxTac" f:ident : tactic => `(tactic|
  (intro rec x y
   simp only [$f:ident, XIndex]
   rcases rec x with m | a <;> simp [Except.bind] <;> (try (rcases rec y with m2 | b)) <;> simp))
macro "okTac" f:ident : tactic => `(tactic|
  (intro θ rec e hi lo
   simp only [$f:ident]
   constructor <;> intro h <;> simp_all))

/-! ## 3. Per-clause statements of the implementation -/
#proves ∀ (θ : Th) (v : Int) (w : Nat), specExprM θ (.const v w) = .ok (.const v w) := intro θ v w; simp [specExprM]
#proves ∀ (θ : Th) (n : String), specExprM θ (.ref n) = .ok (.ref n) := intro θ n; simp [specExprM]
#proves ∀ (θ : Th) (o : Sparkle.IR.AST.Operator) (args : List SE), specExprM θ (.op o args) = XList (specExprsM θ) (.op o) args :=
  intro θ o args; simp only [specExprM, XList]; rcases specExprsM θ args with m | a <;> simp [Except.bind]
#proves ∀ (θ : Th) (args : List SE), specExprM θ (.concat args) = XList (specExprsM θ) .concat args :=
  intro θ args; simp only [specExprM, XList]; rcases specExprsM θ args with m | a <;> simp [Except.bind]
#proves ∀ (θ : Th) (e : SE) (hi lo : Nat), specExprM θ (.slice e hi lo) =
    (match specExprM θ e with | .error m => .error m | .ok a => .ok (.slice a hi lo)) :=
  intro θ e hi lo; simp only [specExprM]; rcases specExprM θ e with m | a <;> simp [Except.bind]
#proves ∀ (θ : Th) (e : SE) (hi lo : DimExpr), specExprM θ (.sliceDim e hi lo) = XSliceDim θ (specExprM θ) e hi lo :=
  intro θ e hi lo; simp only [specExprM, XSliceDim]
  rcases evalM θ hi with m | h <;> rcases evalM θ lo with m2 | l <;> simp [Except.bind] <;>
    (try split) <;> (try (rcases specExprM θ e with m3 | a)) <;> simp
#proves ∀ (θ : Th) (x y : SE), specExprM θ (.index x y) = XIndex (specExprM θ) x y :=
  intro θ x y; simp only [specExprM, XIndex]
  rcases specExprM θ x with m | a <;> simp [Except.bind] <;> (try (rcases specExprM θ y with m2 | b)) <;> simp
#proves ∀ θ : Th, specExprsM θ [] = .ok [] := intro θ; simp [specExprsM]
#proves ∀ (θ : Th) (e : SE) (es : List SE), specExprsM θ (e :: es) =
    (match specExprM θ e with
     | .error m => .error m
     | .ok a => (match specExprsM θ es with | .error m => .error m | .ok b => .ok (a :: b))) :=
  intro θ e es; simp only [specExprsM]; rcases specExprM θ e with m | a <;> simp [Except.bind] <;>
    (try (rcases specExprsM θ es with m2 | b)) <;> simp
-- ExprOK / NoDim clauses (7 each) and list companions
#proves ∀ θ : Th, ∀ (v : Int) (w : Nat), ExprOK θ (.const v w) = True := intro θ v w; simp [ExprOK]
#proves ∀ (θ : Th) (n : String), ExprOK θ (.ref n) = True := intro θ n; simp [ExprOK]
#proves ∀ (θ : Th) (o : Sparkle.IR.AST.Operator) (args : List SE), ExprOK θ (.op o args) = ExprsOK θ args := intro θ o args; simp [ExprOK]
#proves ∀ (θ : Th) (args : List SE), ExprOK θ (.concat args) = ExprsOK θ args := intro θ args; simp [ExprOK]
#proves ∀ (θ : Th) (e : SE) (hi lo : Nat), ExprOK θ (.slice e hi lo) = ExprOK θ e := intro θ e hi lo; simp [ExprOK]
#proves ∀ (θ : Th) (e : SE) (hi lo : DimExpr), ExprOK θ (.sliceDim e hi lo) = (SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ ExprOK θ e) :=
  intro θ e hi lo; simp [ExprOK]
#proves ∀ (θ : Th) (x y : SE), ExprOK θ (.index x y) = (ExprOK θ x ∧ ExprOK θ y) := intro θ x y; simp [ExprOK]
#proves ∀ θ : Th, ExprsOK θ [] = True := intro θ; simp [ExprsOK]
#proves ∀ (θ : Th) (e : SE) (es : List SE), ExprsOK θ (e :: es) = (ExprOK θ e ∧ ExprsOK θ es) := intro θ e es; simp [ExprsOK]
#proves ∀ (v : Int) (w : Nat), NoDim (.const v w) = True := intro v w; simp [NoDim]
#proves ∀ n : String, NoDim (.ref n) = True := intro n; simp [NoDim]
#proves ∀ (o : Sparkle.IR.AST.Operator) (args : List SE), NoDim (.op o args) = NoDims args := intro o args; simp [NoDim]
#proves ∀ args : List SE, NoDim (.concat args) = NoDims args := intro args; simp [NoDim]
#proves ∀ (e : SE) (hi lo : Nat), NoDim (.slice e hi lo) = NoDim e := intro e hi lo; simp [NoDim]
#proves ∀ (e : SE) (hi lo : DimExpr), NoDim (.sliceDim e hi lo) = False := intro e hi lo; simp [NoDim]
#proves ∀ x y : SE, NoDim (.index x y) = (NoDim x ∧ NoDim y) := intro x y; simp [NoDim]
#proves NoDims [] = True := simp [NoDims]
#proves ∀ (e : SE) (es : List SE), NoDims (e :: es) = (NoDim e ∧ NoDims es) := intro e es; simp [NoDims]

/-! ## 4. Def mutants (well-typed single changes; clause bodies with the recursive call as a parameter; the same tactic as the
positive clause statements, against the independent clause bodies XSliceDim / XList / XIndex; rejection by proof failure only,
NOT a semantic counterexample) -/
def MS1 (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  (evalM θ hi).bind fun h => (evalM θ lo).bind fun l =>
    if h ≤ l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
    else (rec e).bind fun a => .ok (.slice a h l)
def MS2 (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  (evalM θ hi).bind fun h => (evalM θ lo).bind fun l =>
    if h > l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
    else (rec e).bind fun a => .ok (.slice a h l)
def MS3 (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  (evalM θ hi).bind fun h => (evalM θ lo).bind fun l => (rec e).bind fun a => .ok (.slice a h l)
def MS4 (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  (evalM θ hi).bind fun h => (evalM θ lo).bind fun l =>
    if h < l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
    else (rec e).bind fun a => .ok (.slice a l h)
def MS5 (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  (evalM θ hi).bind fun h => (evalM θ lo).bind fun l =>
    if h < l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
    else (rec e).bind fun a => .ok (.sliceDim a hi lo)
def MS6 (θ : Th) (_rec : SE → Except String SE) (e : SE) (hi lo : DimExpr) : Except String SE :=
  (evalM θ hi).bind fun h => (evalM θ lo).bind fun l =>
    if h < l then .error s!"invalid specialized slice [{h}:{l}]: high bound is below low bound"
    else .ok (.slice e h l)
def ML1 (recs : List SE → Except String (List SE)) (mk : List SE → SE) (args : List SE) : Except String SE :=
  .ok (mk args)
def ML2 (recs : List SE → Except String (List SE)) (mk : List SE → SE) (args : List SE) : Except String SE :=
  (recs args).bind fun a => .ok (mk a.reverse)
def MI1 (rec : SE → Except String SE) (x y : SE) : Except String SE :=
  (rec x).bind fun a => .ok (.index a y)
def MO1 (θ : Th) (rec : SE → Prop) (e : SE) (hi lo : DimExpr) : Prop := Bound θ hi ∧ Bound θ lo ∧ rec e
def MO2 (θ : Th) (rec : SE → Prop) (e : SE) (hi lo : DimExpr) : Prop := SliceOK hi lo ∧ Bound θ hi ∧ rec e
def MN1 (e : SE) (hi lo : DimExpr) : Prop := True

#not_proves ∀ (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr), MS1 θ rec e hi lo = XSliceDim θ rec e hi lo := sdTac MS1
#not_proves ∀ (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr), MS2 θ rec e hi lo = XSliceDim θ rec e hi lo := sdTac MS2
#not_proves ∀ (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr), MS3 θ rec e hi lo = XSliceDim θ rec e hi lo := sdTac MS3
#not_proves ∀ (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr), MS4 θ rec e hi lo = XSliceDim θ rec e hi lo := sdTac MS4
#not_proves ∀ (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr), MS5 θ rec e hi lo = XSliceDim θ rec e hi lo := sdTac MS5
#not_proves ∀ (θ : Th) (rec : SE → Except String SE) (e : SE) (hi lo : DimExpr), MS6 θ rec e hi lo = XSliceDim θ rec e hi lo := sdTac MS6
#not_proves ∀ (recs : List SE → Except String (List SE)) (mk : List SE → SE) (args : List SE), ML1 recs mk args = XList recs mk args := listTac ML1
#not_proves ∀ (recs : List SE → Except String (List SE)) (mk : List SE → SE) (args : List SE), ML2 recs mk args = XList recs mk args := listTac ML2
#not_proves ∀ (rec : SE → Except String SE) (x y : SE), MI1 rec x y = XIndex rec x y := idxTac MI1
#not_proves ∀ (θ : Th) (rec : SE → Prop) (e : SE) (hi lo : DimExpr), MO1 θ rec e hi lo ↔ (SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ rec e) :=
  intro θ rec e hi lo; simp only [MO1]; constructor <;> intro h <;> simp_all
#not_proves ∀ (θ : Th) (rec : SE → Prop) (e : SE) (hi lo : DimExpr), MO2 θ rec e hi lo ↔ (SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ rec e) :=
  intro θ rec e hi lo; simp only [MO2]; constructor <;> intro h <;> simp_all
#not_proves ∀ (e : SE) (hi lo : DimExpr), MN1 e hi lo ↔ False :=
  intro e hi lo; simp only [MN1]; constructor <;> intro h <;> simp_all

/-! ## 5. Theorem TYPE (independent copies written from freeze §2) -/
#type_defeq specExprM_ok :
  ∀ {θ : Th} {e : SE}, ExprOK θ e → AllPos θ → ∃ e' : SE, specExprM θ e = Except.ok e'
#type_defeq specExprM_noDim :
  ∀ {θ : Th} {e e' : SE}, specExprM θ e = Except.ok e' → NoDim e'
#type_defeq specExprM_startLength :
  ∀ {θ : Th} {src : SE} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ → ExprOK θ src →
    ∃ e' : SE, specExprM θ (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l) = Except.ok e'
#type_defeq agree_spec : ∀ (θ : Th) (e : SE), specExprM θ e = ExpSpec θ e
#type_defeq agree_specs : ∀ (θ : Th) (es : List SE), specExprsM θ es = ExpSpecs θ es
#type_defeq agree_ok : ∀ (θ : Th) (e : SE), ExprOK θ e ↔ ExpOK θ e
#type_defeq agree_oks : ∀ (θ : Th) (es : List SE), ExprsOK θ es ↔ ExpOKs θ es
#type_defeq agree_noDim : ∀ e : SE, NoDim e ↔ ExpNoDim e
#type_defeq agree_noDims : ∀ es : List SE, NoDims es ↔ ExpNoDims es

/-! ## 6. Theorem MUTANT (well-typed single change; signature/defeq rejection, not a semantic counterexample) -/
-- F2a: drop ha
#mutant_rejected specExprM_ok :
  ∀ {θ : Th} {e : SE}, ExprOK θ e → ∃ e' : SE, specExprM θ e = Except.ok e'
-- F2a: drop hok
#mutant_rejected specExprM_ok :
  ∀ {θ : Th} {e : SE}, AllPos θ → ∃ e' : SE, specExprM θ e = Except.ok e'
-- F2a: ExprOK -> NoDim hypothesis
#mutant_rejected specExprM_ok :
  ∀ {θ : Th} {e : SE}, NoDim e → AllPos θ → ∃ e' : SE, specExprM θ e = Except.ok e'
-- F2b: .ok e' -> .error "" (explicit string)
#mutant_rejected specExprM_noDim :
  ∀ {θ : Th} {e : SE} {e' : SE}, specExprM θ e = Except.error "" → NoDim e'
-- F2b: NoDim e' -> NoDim e
#mutant_rejected specExprM_noDim :
  ∀ {θ : Th} {e e' : SE}, specExprM θ e = Except.ok e' → NoDim e
-- F2c: drop hsrc
#mutant_rejected specExprM_startLength :
  ∀ {θ : Th} {src : SE} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    ∃ e' : SE, specExprM θ (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l) = Except.ok e'
-- F2c: drop hl
#mutant_rejected specExprM_startLength :
  ∀ {θ : Th} {src : SE} {s l : DimExpr}, NonNegDim s → Bound θ s ∧ Bound θ l → AllPos θ → ExprOK θ src →
    ∃ e' : SE, specExprM θ (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l) = Except.ok e'
-- F2c: makeSliceFromStartLength -> makeSliceExpr (arguments made concrete)
#mutant_rejected specExprM_startLength :
  ∀ {θ : Th} {src : SE} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ → ExprOK θ src →
    ∃ e' : SE, specExprM θ (Sparkle.Compiler.Elab.makeSliceExpr src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s) = Except.ok e'
-- F2c: drop the conjunct Bound θ l (a conjunction member of the hypothesis)
#mutant_rejected specExprM_startLength :
  ∀ {θ : Th} {src : SE} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s → AllPos θ → ExprOK θ src →
    ∃ e' : SE, specExprM θ (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l) = Except.ok e'

/-! ## 7. AXIOMS and CLOSURE -/
#audit_axioms specExprM_ok
#audit_axioms specExprM_noDim
#audit_axioms specExprM_startLength
#audit_axioms agree_spec
#audit_axioms agree_specs
#audit_axioms agree_ok
#audit_axioms agree_oks
#audit_axioms agree_noDim
#audit_axioms agree_noDims
#audit_closure specExprM_ok
#audit_closure specExprM_noDim
#audit_closure specExprM_startLength
#audit_closure agree_spec
#audit_closure agree_specs
#audit_closure agree_ok
#audit_closure agree_oks
#audit_closure agree_noDim
#audit_closure agree_noDims

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

end Tests.Gen4.ParamBridgeSpecExprCheck
