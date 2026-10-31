import Lean
import Tools.ShippingGen4ParamLayerA
set_option autoImplicit false
-- BUILT (clean issue-linked): par10vb-0d932e22 (Tests.Gen4.ParamLayerACheck + ParamIfaceCheck, kjob lake incremental) exit 0, 707 jobs, approved at 0d932e22. Comment-only update.
-- Directive counts (rule: count of top-level `#...` directive lines per kind; each is one pass/fail assertion, silent on success;
-- the unknown-name fixture is ONE directive running 4 internal cases): type_defeq 6, value_defeq 4, clause_defeq 33 (evalM 11, Bound 11, PosDim 11),
-- mutant_rejected 13 (theorem types; per theorem: mkAdd 1, mkSub_of_le 2, pos 3, nonneg 2, sliceOK_order 3, sub_one 2),
-- value_mutant_rejected 4, clause_rejected 6, audit_axioms 11, audit_closure 11, closure_detects 2, closure_clean 2, sig_clean 2, closure_unknown_fixtures 1.

/-! # Check of Tools/ShippingGen4ParamLayerA.lean against scripts/gen4/PARAMETRIC_LAYERA_FREEZE.md rev2

Expected statements and definition bodies are written here from the freeze text (not copied from the implementation file).
1. TYPE / VALUE: `isDefEq` of the checked constant's type (theorems) or value (definitions) to the independent copy.
2. MUTANT: well-typed single-point changes (a conjunct dropped, a bound flipped, a hypothesis dropped, a clause of a
   definition body changed). The SAME comparator `defeqTo` rejects them. This is a rejection by signature/defeq, NOT a
   semantic counterexample: it does not say the mutated statement is false.
3. AXIOMS: propext / Classical.choice / Quot.sound only. 4. CLOSURE: no `Laws`/`T1Hyp`/`T1HypND`; unknown names fail.
Layer A is a pure model; none of this is a production I5b/T/FG supply. -/

open Lean Elab Command Meta

/-- The single comparator used by every TYPE/VALUE check and every MUTANT check. -/
def defeqTo (a b : Expr) : MetaM Bool := isDefEq a b

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

/-- A definition's VALUE must be defeq to an independent copy. -/
elab "#value_defeq " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  let some v := info.value? | throwError "{n}: no value"
  unless ← defeqTo v ty do throwError "VALUE mismatch for {n}"

/-- A definition body mutant (a changed copy) must NOT be defeq to the checked value. -/
elab "#value_mutant_rejected " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  let some v := info.value? | throwError "{n}: no value"
  if ← defeqTo v ty then throwError "value mutant NOT rejected for {n}"

/-- A recursive definition's body, clause by clause: `lhs = rhs` (an equation between the applied constant and an
independently written right side) must hold by `defeqTo` after introducing the universally quantified variables. -/
elab "#clause_defeq " t:term : command => liftTermElabM do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  forallTelescope ty fun _ body => do
    let some (_, l, r) := body.eq? | throwError "not an equation"
    unless ← defeqTo l r do throwError "CLAUSE mismatch: {l} vs {r}"

/-- A clause mutant (well-typed, one point changed) must be rejected by the same comparator. -/
elab "#clause_rejected " t:term : command => liftTermElabM do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  forallTelescope ty fun _ body => do
    let some (_, l, r) := body.eq? | throwError "not an equation"
    if ← defeqTo l r then throwError "clause mutant NOT rejected: {l}"

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

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamLayerACheck.Fixture.Bad]

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


namespace Tests.Gen4.ParamLayerACheck
open Sparkle.IR.Type Tools.ShippingGen4ParamLayerA

/-! ## 0. Independent Expected copies (written from the freeze text) -/


/-! ## 1. TYPE (theorems) -/
#type_defeq evalM_mkAdd :
  ∀ (θ : List (String × Nat)) (a b : DimExpr),
    evalM θ (DimExpr.mkAdd a b) = evalM θ (DimExpr.add a b)
#type_defeq evalM_mkSub_of_le :
  ∀ {θ : List (String × Nat)} {a b : DimExpr} {x y : Nat},
    evalM θ a = Except.ok x → evalM θ b = Except.ok y → y ≤ x →
    evalM θ (DimExpr.mkSub a b) = Except.ok (x - y)
#type_defeq evalM_pos :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, PosDim e → Bound θ e → AllPos θ →
    ∃ v, evalM θ e = Except.ok v ∧ 0 < v
#type_defeq evalM_nonneg :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, NonNegDim e → Bound θ e → AllPos θ →
    ∃ v, evalM θ e = Except.ok v
#type_defeq sliceOK_order :
  ∀ {θ : List (String × Nat)} {hi lo : DimExpr}, SliceOK hi lo → Bound θ hi ∧ Bound θ lo → AllPos θ →
    ∃ h' l', evalM θ hi = Except.ok h' ∧ evalM θ lo = Except.ok l' ∧ l' ≤ h'
#type_defeq evalM_sub_one_at_one :
  evalM [("n", 1)] (DimExpr.sub (DimExpr.parameter "n") (DimExpr.literal 1)) = Except.ok 0

/-! ## 2. VALUE (non-recursive bodies by value; recursive bodies clause by clause) -/
#value_defeq clog2M : fun (v : Nat) => if v == 1 then 0 else Nat.log2 (v - 1) + 1
#value_defeq AllPos : fun (θ : List (String × Nat)) => ∀ p ∈ θ, 0 < p.2
#value_defeq NonNegDim : fun (e : DimExpr) => e = DimExpr.literal 0 ∨ PosDim e
#value_defeq SliceOK :
  fun (hi lo : DimExpr) => ∃ s l, lo = s ∧
    hi = DimExpr.mkSub (DimExpr.mkAdd s l) (DimExpr.literal 1) ∧ NonNegDim s ∧ PosDim l
-- evalM, 11 clauses
#clause_defeq ∀ θ v, evalM θ (.literal v) = (Except.ok v : Except String Nat)
#clause_defeq ∀ θ n, evalM θ (.parameter n) = (match θ.lookup n with
    | some v => Except.ok v
    | none => Except.error s!"missing specialization binding for parameter '{n}'" : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.add a b) =
  (do let x ← evalM θ a; let y ← evalM θ b; pure (x + y) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.sub a b) =
  (do let x ← evalM θ a; let y ← evalM θ b
      if x < y then throw s!"hardware dimension subtraction underflow: {x} - {y}" else pure (x - y) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.mul a b) =
  (do let x ← evalM θ a; let y ← evalM θ b; pure (x * y) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.div a b) =
  (do let x ← evalM θ a; let y ← evalM θ b
      if y == 0 then throw "hardware dimension division by zero" else pure (x / y) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.mod a b) =
  (do let x ← evalM θ a; let y ← evalM θ b
      if y == 0 then throw "hardware dimension modulo by zero" else pure (x % y) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.pow a b) =
  (do let x ← evalM θ a; let y ← evalM θ b; pure (x ^ y) : Except String Nat)
#clause_defeq ∀ θ a, evalM θ (.clog2 a) =
  (do let x ← evalM θ a
      if x == 0 then throw "clog2 is undefined for hardware dimension 0" else pure (clog2M x) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.min a b) =
  (do let x ← evalM θ a; let y ← evalM θ b; pure (Nat.min x y) : Except String Nat)
#clause_defeq ∀ θ a b, evalM θ (.max a b) =
  (do let x ← evalM θ a; let y ← evalM θ b; pure (Nat.max x y) : Except String Nat)
-- Bound, 11 clauses
#clause_defeq ∀ θ v, Bound θ (.literal v) = True
#clause_defeq ∀ θ n, Bound θ (.parameter n) = (∃ v, θ.lookup n = some v)
#clause_defeq ∀ θ a b, Bound θ (.add a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a b, Bound θ (.sub a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a b, Bound θ (.mul a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a b, Bound θ (.div a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a b, Bound θ (.mod a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a b, Bound θ (.pow a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a, Bound θ (.clog2 a) = Bound θ a
#clause_defeq ∀ θ a b, Bound θ (.min a b) = (Bound θ a ∧ Bound θ b)
#clause_defeq ∀ θ a b, Bound θ (.max a b) = (Bound θ a ∧ Bound θ b)
-- PosDim, 11 clauses
#clause_defeq ∀ c, PosDim (.literal c) = (0 < c)
#clause_defeq ∀ n, PosDim (.parameter n) = True
#clause_defeq ∀ a b, PosDim (.add a b) = (PosDim a ∧ PosDim b)
#clause_defeq ∀ a b, PosDim (.sub a b) = False
#clause_defeq ∀ a b, PosDim (.mul a b) = (PosDim a ∧ PosDim b)
#clause_defeq ∀ a b, PosDim (.div a b) = False
#clause_defeq ∀ a b, PosDim (.mod a b) = False
#clause_defeq ∀ a b, PosDim (.pow a b) = (PosDim a ∧ PosDim b)
#clause_defeq ∀ a, PosDim (.clog2 a) = False
#clause_defeq ∀ a b, PosDim (.min a b) = (PosDim a ∧ PosDim b)
#clause_defeq ∀ a b, PosDim (.max a b) = (PosDim a ∧ PosDim b)

/-! ## 3. MUTANT (signature/defeq REJECTIONS only; none is a semantic counterexample) -/
-- evalM_mkAdd: mkAdd replaced by mkSub on the left
#mutant_rejected evalM_mkAdd :
  ∀ (θ : List (String × Nat)) (a b : DimExpr),
    evalM θ (DimExpr.mkSub a b) = evalM θ (DimExpr.add a b)
-- evalM_mkSub_of_le: hypothesis `y ≤ x` dropped
#mutant_rejected evalM_mkSub_of_le :
  ∀ {θ : List (String × Nat)} {a b : DimExpr} {x y : Nat},
    evalM θ a = Except.ok x → evalM θ b = Except.ok y →
    evalM θ (DimExpr.mkSub a b) = Except.ok (x - y)
-- evalM_mkSub_of_le: result `x - y` -> `x + y`
#mutant_rejected evalM_mkSub_of_le :
  ∀ {θ : List (String × Nat)} {a b : DimExpr} {x y : Nat},
    evalM θ a = Except.ok x → evalM θ b = Except.ok y → y ≤ x →
    evalM θ (DimExpr.mkSub a b) = Except.ok (x + y)
-- evalM_pos: conjunct `0 < v` dropped
#mutant_rejected evalM_pos :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, PosDim e → Bound θ e → AllPos θ →
    ∃ v, evalM θ e = Except.ok v
-- evalM_pos: `0 < v` -> `0 ≤ v`
#mutant_rejected evalM_pos :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, PosDim e → Bound θ e → AllPos θ →
    ∃ v, evalM θ e = Except.ok v ∧ 0 ≤ v
-- evalM_pos: AllPos hypothesis dropped
#mutant_rejected evalM_pos :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, PosDim e → Bound θ e →
    ∃ v, evalM θ e = Except.ok v ∧ 0 < v
-- evalM_nonneg: Bound hypothesis dropped
#mutant_rejected evalM_nonneg :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, NonNegDim e → AllPos θ →
    ∃ v, evalM θ e = Except.ok v
-- evalM_nonneg: NonNegDim -> PosDim
#mutant_rejected evalM_nonneg :
  ∀ {θ : List (String × Nat)} {e : DimExpr}, PosDim e → Bound θ e → AllPos θ →
    ∃ v, evalM θ e = Except.ok v
-- sliceOK_order: conjunct `l' ≤ h'` dropped
#mutant_rejected sliceOK_order :
  ∀ {θ : List (String × Nat)} {hi lo : DimExpr}, SliceOK hi lo → Bound θ hi ∧ Bound θ lo → AllPos θ →
    ∃ h' l', evalM θ hi = Except.ok h' ∧ evalM θ lo = Except.ok l'
-- sliceOK_order: `l' ≤ h'` -> `h' ≤ l'`
#mutant_rejected sliceOK_order :
  ∀ {θ : List (String × Nat)} {hi lo : DimExpr}, SliceOK hi lo → Bound θ hi ∧ Bound θ lo → AllPos θ →
    ∃ h' l', evalM θ hi = Except.ok h' ∧ evalM θ lo = Except.ok l' ∧ h' ≤ l'
-- sliceOK_order: hi and lo swapped in the SliceOK premise
#mutant_rejected sliceOK_order :
  ∀ {θ : List (String × Nat)} {hi lo : DimExpr}, SliceOK lo hi → Bound θ hi ∧ Bound θ lo → AllPos θ →
    ∃ h' l', evalM θ hi = Except.ok h' ∧ evalM θ lo = Except.ok l' ∧ l' ≤ h'
-- evalM_sub_one_at_one: `.ok 0` -> `.ok 1`
#mutant_rejected evalM_sub_one_at_one :
  evalM [("n", 1)] (DimExpr.sub (DimExpr.parameter "n") (DimExpr.literal 1)) = Except.ok 1
-- evalM_sub_one_at_one: n = 1 -> n = 2
#mutant_rejected evalM_sub_one_at_one :
  evalM [("n", 2)] (DimExpr.sub (DimExpr.parameter "n") (DimExpr.literal 1)) = Except.ok 0
-- definition BODY mutants (well-typed copies; each differs at one point)
#clause_rejected ∀ θ a b, evalM θ (.sub a b) =
  (do let x ← evalM θ a; let y ← evalM θ b
      if x ≤ y then throw s!"hardware dimension subtraction underflow: {x} - {y}" else pure (x - y) : Except String Nat)
#clause_rejected ∀ θ a b, evalM θ (.sub a b) =
  (do let x ← evalM θ a; let y ← evalM θ b
      if x < y then throw "hardware dimension subtraction underflow" else pure (x - y) : Except String Nat)
#clause_rejected ∀ θ a b, evalM θ (.add a b) =
  (do let x ← evalM θ a; let y ← evalM θ b; pure (x * y) : Except String Nat)
#clause_rejected ∀ θ a b, Bound θ (.add a b) = (Bound θ a ∨ Bound θ b)
#clause_rejected ∀ c, PosDim (.literal c) = (0 ≤ c)
#clause_rejected ∀ a b, PosDim (.min a b) = (PosDim a ∨ PosDim b)
#value_mutant_rejected clog2M : fun (v : Nat) => if v == 0 then 0 else Nat.log2 (v - 1) + 1
#value_mutant_rejected AllPos : fun (θ : List (String × Nat)) => ∀ p ∈ θ, 0 ≤ p.2
#value_mutant_rejected SliceOK :
  fun (hi lo : DimExpr) => ∃ s l, lo = s ∧ hi = DimExpr.sub (DimExpr.add s l) (DimExpr.literal 1) ∧
    NonNegDim s ∧ PosDim l
#value_mutant_rejected NonNegDim : fun (e : DimExpr) => PosDim e

/-! ## 4. AXIOMS and CLOSURE -/
#audit_axioms lookup_mem
#audit_axioms Bound_mkAdd
#audit_axioms Bound_mkSub
#audit_axioms evalM_mkAdd
#audit_axioms evalM_mkSub_of_le
#audit_axioms evalM_pos
#audit_axioms evalM_nonneg
#audit_axioms sliceOK_order
#audit_axioms evalM_sub_one_at_one
#audit_axioms evalM
#audit_axioms SliceOK
#audit_closure lookup_mem
#audit_closure Bound_mkAdd
#audit_closure Bound_mkSub
#audit_closure evalM_mkAdd
#audit_closure evalM_mkSub_of_le
#audit_closure evalM_pos
#audit_closure evalM_nonneg
#audit_closure sliceOK_order
#audit_closure evalM_sub_one_at_one
#audit_closure evalM
#audit_closure SliceOK

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

end Tests.Gen4.ParamLayerACheck
