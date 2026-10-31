import Lean
import Tools.ShippingGen4ParamBridgeCompose
set_option autoImplicit false
-- BUILT: clean issue-linked build par14v-40bc5ec0 (Tests.Gen4.ParamBridgeComposeCheck, kjob lake incremental) exit 0, 229 jobs, approved at 40bc5ec0. Comment-only update.
-- Directive counts (rule: count of top-level `#...` directive lines per kind; each is one pass/fail assertion, silent on success;
-- the unknown-name fixture is ONE directive running 4 internal cases): type_defeq 3, mutant_rejected 9
-- (startLength_node_ordered 7, Bound_of_mkAdd 1, Bound_of_mkSub 1), audit_axioms 3, audit_closure 3,
-- closure_detects 2, closure_clean 2, sig_clean 2, closure_unknown_fixtures 1.
-- Closure limitation: opaque bodies (DimExpr.evaluate, specializeType, specializeExpr) are NOT followed by the
-- `getUsedConstants`-based closure; only their types are. Opaque constants reached are logged.

/-! # Check of Tools/ShippingGen4ParamBridgeCompose.lean against scripts/gen4/PARAMETRIC_BRIDGE_UNIT2_FREEZE.md §2-§3

Expected statements are written here from the freeze text (not copied from the implementation file).
1. TYPE: `isDefEq` (reducible) of the checked theorem's type to the independent copy.
2. MUTANT: well-typed single-point changes rejected by the SAME comparator `defeqTo`: a rejection by signature/defeq,
   NOT a semantic counterexample. 3. AXIOMS: propext / Classical.choice / Quot.sound only. 4. CLOSURE as in ParamBridgeShapeCheck.
Not a production I5b / T / FG supply; B1-B4 are unsupplied. -/

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

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamBridgeComposeCheck.Fixture.Bad]

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


namespace Tests.Gen4.ParamBridgeComposeCheck
open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeCompose

/-! ## 1. TYPE -/
#type_defeq startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ l' ≤ h') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
#type_defeq Bound_of_mkAdd :
  ∀ {θ : List (String × Nat)} {a b : DimExpr}, Bound θ a → Bound θ b → Bound θ (DimExpr.mkAdd a b)
#type_defeq Bound_of_mkSub :
  ∀ {θ : List (String × Nat)} {a b : DimExpr}, Bound θ a → Bound θ b → Bound θ (DimExpr.mkSub a b)

/-! ## 2. MUTANT (well-typed single change; signature/defeq rejection only, not a semantic counterexample) -/
-- D1: drop node-shape conjunct of disjunct 1
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    (∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ l' ≤ h') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- D1: drop ordering conjunct l' ≤ h' (replace by True)
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ True) ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- D1: l' ≤ h' -> h' ≤ l'
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ h' ≤ l') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- D1: sliceDim -> slice (well-typed: literal bounds 0 0)
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src 0 0 ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ l' ≤ h') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- D1: drop hl
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → Bound θ s ∧ Bound θ l → AllPos θ →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ l' ≤ h') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- D1: drop hs
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, PosDim l → Bound θ s ∧ Bound θ l → AllPos θ →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ l' ≤ h') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- D1: drop ha
#mutant_rejected startLength_node_ordered :
  ∀ {θ : List (String × Nat)} {src : Sparkle.IR.AST.Expr} {s l : DimExpr}, NonNegDim s → PosDim l → Bound θ s ∧ Bound θ l →
    (Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.sliceDim src (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) s ∧ ∃ h' l' : Nat, evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok h' ∧ evalM θ s = Except.ok l' ∧ l' ≤ h') ∨
    (∃ a b : Nat, Sparkle.Compiler.Elab.makeSliceFromStartLength src s l = Sparkle.IR.AST.Expr.slice src a b ∧ evalM θ (DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1)) = Except.ok a ∧ evalM θ s = Except.ok b ∧ b ≤ a)
-- helper: mkAdd -> mkSub in the conclusion
#mutant_rejected Bound_of_mkAdd :
  ∀ {θ : List (String × Nat)} {a b : DimExpr}, Bound θ a → Bound θ b → Bound θ (DimExpr.mkSub a b)
-- helper: hb dropped
#mutant_rejected Bound_of_mkSub :
  ∀ {θ : List (String × Nat)} {a b : DimExpr}, Bound θ a → Bound θ (DimExpr.mkSub a b)

/-! ## 3. AXIOMS and CLOSURE -/
#audit_axioms startLength_node_ordered
#audit_axioms Bound_of_mkAdd
#audit_axioms Bound_of_mkSub
#audit_closure startLength_node_ordered
#audit_closure Bound_of_mkAdd
#audit_closure Bound_of_mkSub

/-! ## 5. CLOSURE detector fixtures (same detector, fixture-only forbidden name; unknown names fail) -/
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

end Tests.Gen4.ParamBridgeComposeCheck
