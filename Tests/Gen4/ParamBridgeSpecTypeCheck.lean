import Lean
import Tools.ShippingGen4ParamBridgeSpecType
set_option autoImplicit false
-- NOT BUILT: Check of Tools/ShippingGen4ParamBridgeSpecType.lean (scripts/gen4/PARAMETRIC_BRIDGE_UNIT4_FREEZE.md §3). Build result is recorded by the coder.
-- Directive counts, measured (rule: top-level `#...` directive lines per kind, each one pass/fail assertion, silent on success;
-- the unknown-name fixture is ONE directive running 4 internal cases): proves 13 (clause statements of the 4 defs; plus theorem
-- clause_spec_dim for the bitVectorDim clause), not_proves 11 (def mutants), type_defeq 6, mutant_rejected 8 (theorem mutants),
-- audit_axioms 6, audit_closure 6, closure_detects 2, closure_clean 2, sig_clean 2, closure_unknown_fixtures 1. Agreement theorems: 4
-- (agree_req/agree_spec/agree_tyPos/agree_tyBound). No sorry, no native_decide.
-- Closure limitation: opaque bodies (DimExpr.evaluate, specializeType, specializeExpr) are NOT followed by the
-- `getUsedConstants`-based closure; only their types are. Opaque constants reached are logged.

/-! # Check of Tools/ShippingGen4ParamBridgeSpecType.lean against scripts/gen4/PARAMETRIC_BRIDGE_UNIT4_FREEZE.md §3

Expected definitions `ExpReq/ExpSpec/ExpTyPos/ExpTyBound` are written here from freeze §2/§3.1 text (explicit `match`, no
reference to the implementation constants). The four implementation definitions are compared to them by full-argument
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

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamBridgeSpecTypeCheck.Fixture.Bad]

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

namespace Tests.Gen4.ParamBridgeSpecTypeCheck
open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeShape Tools.ShippingGen4ParamBridgeWidth
  Tools.ShippingGen4ParamBridgeSpecType

/-! ## 0. Independent Expected definitions (freeze §3.1; explicit `match`, no implementation constants) -/
def ExpReq (c : String) (v : Nat) : Except String Nat :=
  match v with
  | 0 => .error s!"{c} specializes to zero width"
  | n+1 => .ok (n+1)

def ExpSpec (θ : List (String × Nat)) (c : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector w => .ok (.bitVector w)
  | .bitVectorDim d =>
      match evalM θ d with
      | .error m => .error m
      | .ok w =>
        match ExpReq c w with
        | .error m => .error m
        | .ok w' => .ok (hwTypeFromWidth w')
  | .array n e =>
      match ExpSpec θ s!"{c} element" e with
      | .error m => .error m
      | .ok e' => .ok (.array n e')

def ExpTyPos : HWType → Prop
  | .bit => True
  | .bitVector _ => True
  | .bitVectorDim d => PosDim d
  | .array _ e => ExpTyPos e

def ExpTyBound (θ : List (String × Nat)) : HWType → Prop
  | .bit => True
  | .bitVector _ => True
  | .bitVectorDim d => Bound θ d
  | .array _ e => ExpTyBound θ e

/-! ## 1. Full-argument agreement theorems (all arguments quantified, all clauses) -/
theorem agree_req : ∀ (c : String) (v : Nat), requirePositiveM c v = ExpReq c v := by
  intro c v; cases v <;> simp [requirePositiveM, ExpReq]

macro "reqTac" f:ident : tactic => `(tactic| (intro c v; cases v <;> simp [$f:ident, ExpReq]))

macro "specTac" f:ident : tactic => `(tactic|
  (intro θ c t
   induction t generalizing c with
   | bit => simp [$f:ident, ExpSpec]
   | bitVector w => simp [$f:ident, ExpSpec]
   | bitVectorDim d =>
     cases h : evalM θ d with
     | error m => simp [$f:ident, ExpSpec, h, Except.bind]
     | ok w =>
       simp [$f:ident, ExpSpec, h, Except.bind, agree_req]
       cases ExpReq c w <;> simp
   | array n e ih =>
     cases h : ExpSpec θ s!"{c} element" e with
     | error m => simp [$f:ident, ExpSpec, h, ih, Except.bind]
     | ok e' => simp [$f:ident, ExpSpec, h, ih, Except.bind]))

macro "posTac" f:ident g:ident : tactic => `(tactic|
  (intro t
   induction t with
   | bit => simp [$f:ident, $g:ident]
   | bitVector w => simp [$f:ident, $g:ident]
   | bitVectorDim d => simp [$f:ident, $g:ident]
   | array n e ih => simp [$f:ident, $g:ident, ih]))

macro "boundTac" f:ident g:ident : tactic => `(tactic|
  (intro θ t
   induction t with
   | bit => simp [$f:ident, $g:ident]
   | bitVector w => simp [$f:ident, $g:ident]
   | bitVectorDim d => simp [$f:ident, $g:ident]
   | array n e ih => simp [$f:ident, $g:ident, ih]))

theorem agree_spec : ∀ (θ : List (String × Nat)) (c : String) (t : HWType), specTypeM θ c t = ExpSpec θ c t := by
  specTac specTypeM
theorem agree_tyPos : ∀ t : HWType, TyPos t ↔ ExpTyPos t := by posTac TyPos ExpTyPos
theorem agree_tyBound : ∀ (θ : List (String × Nat)) (t : HWType), TyBound θ t ↔ ExpTyBound θ t := by
  boundTac TyBound ExpTyBound

/-! ## 2. Per-clause statements of the implementation (same tactic path as the mutants) -/
-- requirePositiveM (2 clauses: 0 / n+1)
#proves ∀ c : String, requirePositiveM c 0 = .error s!"{c} specializes to zero width" := intro c; simp [requirePositiveM]
#proves ∀ (c : String) (n : Nat), requirePositiveM c (n+1) = .ok (n+1) := intro c n; simp [requirePositiveM]
-- specTypeM (4 clauses)
#proves ∀ (θ : List (String × Nat)) (c : String), specTypeM θ c .bit = .ok .bit := intro θ c; simp [specTypeM]
#proves ∀ (θ : List (String × Nat)) (c : String) (w : Nat), specTypeM θ c (.bitVector w) = .ok (.bitVector w) := intro θ c w; simp [specTypeM]
theorem clause_spec_dim : ∀ (θ : List (String × Nat)) (c : String) (d : DimExpr), specTypeM θ c (.bitVectorDim d) =
    (match evalM θ d with
     | .error m => .error m
     | .ok w => match ExpReq c w with | .error m => .error m | .ok w' => .ok (hwTypeFromWidth w')) := by
  intro θ c d
  cases h : evalM θ d with
  | error m => simp [specTypeM, h, Except.bind]
  | ok w =>
    simp [specTypeM, h, Except.bind, agree_req]
    cases ExpReq c w <;> simp
#proves ∀ (θ : List (String × Nat)) (c : String) (n : Nat) (e : HWType), specTypeM θ c (.array n e) =
    (match specTypeM θ s!"{c} element" e with | .error m => .error m | .ok e' => .ok (.array n e')) := intro θ c n e; simp [specTypeM]; cases h : specTypeM θ s!"{c} element" e <;> simp [Except.bind]
-- TyPos / TyBound (4 clauses each)
#proves TyPos .bit = True := simp [TyPos]
#proves ∀ w : Nat, TyPos (.bitVector w) = True := intro w; simp [TyPos]
#proves ∀ d : DimExpr, TyPos (.bitVectorDim d) = PosDim d := intro d; simp [TyPos]
#proves ∀ (n : Nat) (e : HWType), TyPos (.array n e) = TyPos e := intro n e; simp [TyPos]
#proves ∀ θ : List (String × Nat), TyBound θ .bit = True := intro θ; simp [TyBound]
#proves ∀ (θ : List (String × Nat)) (w : Nat), TyBound θ (.bitVector w) = True := intro θ w; simp [TyBound]
#proves ∀ (θ : List (String × Nat)) (d : DimExpr), TyBound θ (.bitVectorDim d) = Bound θ d := intro θ d; simp [TyBound]
#proves ∀ (θ : List (String × Nat)) (n : Nat) (e : HWType), TyBound θ (.array n e) = TyBound θ e := intro θ n e; simp [TyBound]

/-! ## 3. Def mutants (well-typed single changes; run through the agreement tactics; signature/proof rejection only,
NOT a semantic counterexample) -/
-- zero judgment (2)
def MReq1 (c : String) (v : Nat) : Except String Nat := if v == 1 then .error s!"{c} specializes to zero width" else .ok v
def MReq2 (c : String) (v : Nat) : Except String Nat := if decide (v < 0) then .error s!"{c} specializes to zero width" else .ok v
-- array recursion (3) and other specTypeM clauses (2)
def MSpecA (θ : Binding) (c : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector w => .ok (.bitVector w)
  | .bitVectorDim d => (evalM θ d).bind fun w => (requirePositiveM c w).bind fun w' => .ok (hwTypeFromWidth w')
  | .array n e => .ok (.array n e)
def MSpecB (θ : Binding) (c : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector w => .ok (.bitVector w)
  | .bitVectorDim d => (evalM θ d).bind fun w => (requirePositiveM c w).bind fun w' => .ok (hwTypeFromWidth w')
  | .array n e => (MSpecB θ c e).bind fun e' => .ok (.array n e')
def MSpecC (θ : Binding) (c : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector w => .ok (.bitVector w)
  | .bitVectorDim d => (evalM θ d).bind fun w => (requirePositiveM c w).bind fun w' => .ok (hwTypeFromWidth w')
  | .array _ e => (MSpecC θ s!"{c} element" e).bind fun e' => .ok e'
def MSpecD (θ : Binding) (c : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector w => .ok (.bitVector w)
  | .bitVectorDim d => (evalM θ d).bind fun w => .ok (hwTypeFromWidth w)
  | .array n e => (MSpecD θ s!"{c} element" e).bind fun e' => .ok (.array n e')
def MSpecE (θ : Binding) (c : String) : HWType → Except String HWType
  | .bit => .ok .bit
  | .bitVector w => .ok (.bitVector w)
  | .bitVectorDim d => (evalM θ d).bind fun w => (requirePositiveM c w).bind fun w' => .ok (.bitVector w')
  | .array n e => (MSpecE θ s!"{c} element" e).bind fun e' => .ok (.array n e')
-- TyPos (2) / TyBound (2)
def MPos1 : HWType → Prop
  | .bit => True | .bitVector _ => True | .bitVectorDim _ => True | .array _ e => MPos1 e
def MPos2 : HWType → Prop
  | .bit => True | .bitVector _ => True | .bitVectorDim d => PosDim d | .array _ _ => True
def MBound1 (θ : Binding) : HWType → Prop
  | .bit => True | .bitVector _ => True | .bitVectorDim _ => True | .array _ e => MBound1 θ e
def MBound2 (θ : Binding) : HWType → Prop
  | .bit => True | .bitVector _ => True | .bitVectorDim d => Bound θ d | .array _ _ => True

-- the same statement shapes and the same tactics as the positive agreement theorems
#not_proves ∀ (c : String) (v : Nat), MReq1 c v = ExpReq c v := reqTac MReq1
#not_proves ∀ (c : String) (v : Nat), MReq2 c v = ExpReq c v := reqTac MReq2
#not_proves ∀ (θ : List (String × Nat)) (c : String) (t : HWType), MSpecA θ c t = ExpSpec θ c t := specTac MSpecA
#not_proves ∀ (θ : List (String × Nat)) (c : String) (t : HWType), MSpecB θ c t = ExpSpec θ c t := specTac MSpecB
#not_proves ∀ (θ : List (String × Nat)) (c : String) (t : HWType), MSpecC θ c t = ExpSpec θ c t := specTac MSpecC
#not_proves ∀ (θ : List (String × Nat)) (c : String) (t : HWType), MSpecD θ c t = ExpSpec θ c t := specTac MSpecD
#not_proves ∀ (θ : List (String × Nat)) (c : String) (t : HWType), MSpecE θ c t = ExpSpec θ c t := specTac MSpecE
#not_proves ∀ t : HWType, MPos1 t ↔ ExpTyPos t := posTac MPos1 ExpTyPos
#not_proves ∀ t : HWType, MPos2 t ↔ ExpTyPos t := posTac MPos2 ExpTyPos
#not_proves ∀ (θ : List (String × Nat)) (t : HWType), MBound1 θ t ↔ ExpTyBound θ t := boundTac MBound1 ExpTyBound
#not_proves ∀ (θ : List (String × Nat)) (t : HWType), MBound2 θ t ↔ ExpTyBound θ t := boundTac MBound2 ExpTyBound

/-! ## 4. Theorem TYPE (independent copies written from freeze §2) -/
#type_defeq specTypeM_ok :
  ∀ {θ : List (String × Nat)} {t : HWType} (context : String), TyPos t → TyBound θ t → AllPos θ →
    ∃ t' : HWType, specTypeM θ context t = Except.ok t'
#type_defeq specTypeM_hwTypeFromDim :
  ∀ {θ : List (String × Nat)} {d : DimExpr} (context : String), PosDim d → Bound θ d → AllPos θ →
    ∃ w : Nat, evalM θ d = Except.ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = Except.ok (hwTypeFromWidth w)
#type_defeq agree_req : ∀ (c : String) (v : Nat), requirePositiveM c v = ExpReq c v
#type_defeq agree_spec : ∀ (θ : List (String × Nat)) (c : String) (t : HWType), specTypeM θ c t = ExpSpec θ c t
#type_defeq agree_tyPos : ∀ t : HWType, TyPos t ↔ ExpTyPos t
#type_defeq agree_tyBound : ∀ (θ : List (String × Nat)) (t : HWType), TyBound θ t ↔ ExpTyBound θ t

/-! ## 5. Theorem MUTANT (well-typed single change; signature/defeq rejection, not a semantic counterexample) -/
-- F1a: drop hp
#mutant_rejected specTypeM_ok :
  ∀ {θ : List (String × Nat)} {t : HWType} (context : String), TyBound θ t → AllPos θ →
    ∃ t' : HWType, specTypeM θ context t = Except.ok t'
-- F1a: TyBound -> TyPos in the hypothesis
#mutant_rejected specTypeM_ok :
  ∀ {θ : List (String × Nat)} {t : HWType} (context : String), TyPos t → TyPos t → AllPos θ →
    ∃ t' : HWType, specTypeM θ context t = Except.ok t'
-- F1a: ∃ t' -> ∃ t', ... ∧ t' = t
#mutant_rejected specTypeM_ok :
  ∀ {θ : List (String × Nat)} {t : HWType} (context : String), TyPos t → TyBound θ t → AllPos θ →
    ∃ t' : HWType, specTypeM θ context t = Except.ok t' ∧ t' = t
-- F1b: 0 < w -> 0 ≤ w
#mutant_rejected specTypeM_hwTypeFromDim :
  ∀ {θ : List (String × Nat)} {d : DimExpr} (context : String), PosDim d → Bound θ d → AllPos θ →
    ∃ w : Nat, evalM θ d = Except.ok w ∧ 0 ≤ w ∧ specTypeM θ context (hwTypeFromDim d) = Except.ok (hwTypeFromWidth w)
-- F1b: hwTypeFromWidth w -> .bitVectorDim d
#mutant_rejected specTypeM_hwTypeFromDim :
  ∀ {θ : List (String × Nat)} {d : DimExpr} (context : String), PosDim d → Bound θ d → AllPos θ →
    ∃ w : Nat, evalM θ d = Except.ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = Except.ok (HWType.bitVectorDim d)
-- F1b: drop hb
#mutant_rejected specTypeM_hwTypeFromDim :
  ∀ {θ : List (String × Nat)} {d : DimExpr} (context : String), PosDim d → AllPos θ →
    ∃ w : Nat, evalM θ d = Except.ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = Except.ok (hwTypeFromWidth w)
-- F1b: drop ha
#mutant_rejected specTypeM_hwTypeFromDim :
  ∀ {θ : List (String × Nat)} {d : DimExpr} (context : String), PosDim d → Bound θ d →
    ∃ w : Nat, evalM θ d = Except.ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = Except.ok (hwTypeFromWidth w)
-- F1b: evalM θ d -> evalM [] d
#mutant_rejected specTypeM_hwTypeFromDim :
  ∀ {θ : List (String × Nat)} {d : DimExpr} (context : String), PosDim d → Bound θ d → AllPos θ →
    ∃ w : Nat, evalM [] d = Except.ok w ∧ 0 < w ∧ specTypeM θ context (hwTypeFromDim d) = Except.ok (hwTypeFromWidth w)

/-! ## 6. AXIOMS and CLOSURE -/
#audit_axioms specTypeM_ok
#audit_axioms specTypeM_hwTypeFromDim
#audit_axioms agree_req
#audit_axioms agree_spec
#audit_axioms agree_tyPos
#audit_axioms agree_tyBound
#audit_closure specTypeM_ok
#audit_closure specTypeM_hwTypeFromDim
#audit_closure agree_req
#audit_closure agree_spec
#audit_closure agree_tyPos
#audit_closure agree_tyBound

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

end Tests.Gen4.ParamBridgeSpecTypeCheck
