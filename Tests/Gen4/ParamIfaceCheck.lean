import Tools.ShippingGen4ParamIface
import Tools.ShippingGen4ParamKeeps
set_option autoImplicit false
-- BUILT: clean issue-linked build par6v-41ad0be7 (Tests.Gen4.ParamIfaceCheck) exit 0, 705 jobs, at 41ad0be7. Comment-only update.

/-! # Audit of Tools/ShippingGen4ParamIface.lean and Tools/ShippingGen4ParamKeeps.lean (PARAMETRIC_FREEZE.md rev4 §11.2, §11.3, §11.5)

1. TYPE: each theorem's type (and each definition's value) is `isDefEq` to an independent copy written here from the freeze.
2. MUTANT: signature/defeq REJECTIONS only. A mutant that is not defeq to the checked type is rejected; this is NOT a
   semantic counterexample and says nothing about whether the mutated statement is true.
3. AXIOMS: only propext / Classical.choice / Quot.sound; no sorryAx, no `ofReduceBool` (native_decide).
4. CLOSURE: transitive constant closure (types plus `thmInfo.value`/`defnInfo.value`; `opaque` bodies are not tracked and
   are logged) has no `Laws`, `T1Hyp`, `T1HypND` constant. Section 5 runs proof-only negative (direct, via other-namespace
   helper) and positive fixtures through the same detector.
Scope: I4-struct is a decomposition (which `b` from which `raw`), not an equivalence. The definitions are definitions only.
I3c is the OUTERMOST symbolic run (keeps at general depth D; worlds/balance at depth 0). -/

open Lean Elab Command Meta

elab "#type_defeq " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  unless ← isDefEq info.type ty do throwError "TYPE mismatch for {n}"

elab "#mutant_rejected " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  if ← isDefEq info.type ty then throwError "mutant NOT rejected for {n}"

elab "#audit_axioms " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let axs ← collectAxioms n
  let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless bad.isEmpty do throwError "{n}: axioms {bad}"

/-- Transitive constant closure. The body is fetched explicitly per `ConstantInfo` kind:
`thmInfo.value` and `defnInfo.value` are traversed; `opaqueInfo` bodies are NOT tracked (only the type is), and the
opaque constants reached are returned so the log can state it. Other kinds (axiom, inductive, ctor, rec, quot) have
no body, only a type. Returns (seen, opaque constants reached). -/
private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) (opq : NameSet) :
    NameSet × NameSet :=
  match todo with
  | [] => (seen, opq)
  | n :: rest =>
    if seen.contains n then closure env rest seen opq else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen opq
    | some ci =>
      let (body, opq) : List Name × NameSet := match ci with
        | .thmInfo v => (v.value.getUsedConstants.toList, opq)
        | .defnInfo v => (v.value.getUsedConstants.toList, opq)
        | .opaqueInfo _ => ([], opq.insert n)
        | _ => ([], opq)
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen opq

/-- The one detector, used by production checks and by the fixtures. -/
private def closureReport (forbidden : List Name) (n : Name) : CoreM (List Name × List Name) := do
  let env ← getEnv
  let (seen, opq) := closure env [n] {} {}
  return (seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m, opq.toList)

private def prodForbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamIfaceCheck.Fixture.Bad]

elab "#audit_closure " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let (bad, opq) ← closureReport prodForbidden n
  unless opq.isEmpty do logInfo m!"CLOSURE {n}: opaque bodies NOT tracked (type only): {opq}"
  unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"

/-- Fixture must be flagged by the same detector (fixture-only forbidden name). -/
elab "#closure_detects " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let (bad, _) ← closureReport fixtureForbidden n
  if bad.isEmpty then throwError "{n}: detector MISSED the forbidden constant"

/-- Fixture must not be flagged by the same detector. -/
elab "#closure_clean " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let (bad, _) ← closureReport fixtureForbidden n
  unless bad.isEmpty do throwError "{n}: detector flagged a clean fixture: {bad}"

/-- The fixture's signature must not itself mention the forbidden name (only the proof may). -/
elab "#sig_clean " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let ci ← getConstInfo n
  if ci.type.getUsedConstants.any (fixtureForbidden.contains ·) then throwError "{n}: signature mentions forbidden name"


/-- A definition's VALUE must be defeq to an independent copy. -/
elab "#value_defeq " c:ident " : " t:term : command => liftTermElabM do
  let ty ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  let some v := info.value? | throwError "{n}: no value"
  unless ← isDefEq v ty do throwError "VALUE mismatch for {n}"

/-- The value mentions the file-private `validateBindings` (by its mangled name). -/
elab "#mentions_private_validate " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  let some v := info.value? | throwError "{n}: no value"
  let target := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.validateBindings
  unless v.getUsedConstants.contains target do throwError "{n}: does not mention validateBindings"

namespace Tests.Gen4.ParamIfaceCheck
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildBalance
open Tools.ShippingGen4ParamEntry (Tsyn)
open Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamKeeps

/-! ## 1. TYPE -/
-- I4-struct
#type_defeq synthesizeCombinationalWithParameters_designTop :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Design},
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w' →
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      D'.topModule = D.topModule ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules)
-- legality of a successful specialization
#type_defeq specializeDesign_ok_legal :
  ∀ {design D' : Design} {θ : List (String × Nat)},
    Sparkle.IR.Specialize.specializeDesign design θ = .ok D' → LegalBinding design θ
-- I3c
#type_defeq body_symbolic_keeps :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (D : Nat) (_hC : ChildKeeps L D)
    (b : Bool) (declName : Name) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {tenv : Lean.Environment},
    Keeps mctx mref cctx cref (J L D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName parameters true true ci isInst)
#type_defeq core_symbolic_keeps :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (D : Nat) (declName : Name)
    (parameters : List (String × Nat)) (_hA0 : D = 0 → L.aux {}),
    (∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst)) →
    Keeps mctx mref cctx cref (J L D)
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
#type_defeq core_symbolic_worlds :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (_hA : L.aux {}) {declName : Name}
    {parameters : List (String × Nat)} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design},
    Out0 L w →
    (∀ {tenv : Lean.Environment} (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst)) →
    RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      mctx mref cctx cref w (M, D) w' →
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4 ∧
      J L 1 w3 ∧ J L 1 w4 ∧ J L 0 w'
#type_defeq core_symbolic_balance :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (declName : Name)
    (parameters : List (String × Nat)) {w : Void IO.RealWorld},
    StartV L w → L.quiet w → L.dval w = 0 →
    Out0 L (endW mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) w) ∧
    ErrOk mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) w

-- definitions (VALUE copies)
#type_defeq TopIface.mk :
  List (Name × MixedGateBinder) → List Sparkle.IR.Machine.OutField →
    ((Nat → List Nat) → List (Nat → Nat)) → TopIface
#value_defeq CombTopRunN :
  fun (D' : Design) (n : Nat) (b' : Sparkle.IR.AST.Module) (I : TopIface) =>
    Tools.ShippingGen2.CombChildRunN (Tools.ShippingMachineLinked.childMap D'.modules) D' n b' I.bsC I.outsC I.S
#value_defeq SpecOk :
  fun (D : Design) (θ : List (String × Nat)) => ∃ D', Sparkle.IR.Specialize.specializeDesign D θ = .ok D'
#value_defeq ParamTopShips :
  fun (b : Sparkle.IR.AST.Module) (D : Design) (src : SrcAt) =>
    ∀ θ, LegalBinding (D.addModule b) θ →
      ∀ D', Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →
        ∃ n b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' (src θ)
#value_defeq SpecSuccessAllPositive :
  fun (b : Sparkle.IR.AST.Module) (D : Design) =>
    ((D.addModule b).findModule (D.addModule b).topModule).isSome = true →
      ∀ θ, LegalBinding (D.addModule b) θ → SpecOk (D.addModule b) θ
#value_defeq PostTransfer :
  fun (raw b : Sparkle.IR.AST.Module) (Dr D : Design) (I : TopIface) =>
    ∀ (θ : List (String × Nat)) (Dr' D' : Design),
      Sparkle.IR.Specialize.specializeDesign (Dr.addModule raw) θ = .ok Dr' →
      Sparkle.IR.Specialize.specializeDesign (D.addModule b) θ = .ok D' →
      ∀ (n : Nat) (raw' : Sparkle.IR.AST.Module), Dr'.findModule raw.name = some raw' →
        CombTopRunN Dr' n raw' I →
        ∃ b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' I
#mentions_private_validate LegalBinding

/-! ## 2. MUTANT (signature/defeq rejections, NOT semantic counterexamples) -/
-- I4-struct: `∨` between the two post-processing outcomes replaced by `∧`
#mutant_rejected synthesizeCombinationalWithParameters_designTop :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Design},
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w' →
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
        M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      D'.topModule = D.topModule ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules)
-- I3c worlds: the final world at depth 1 instead of 0
#mutant_rejected core_symbolic_worlds :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (_hA : L.aux {}) {declName : Name}
    {parameters : List (String × Nat)} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design},
    Out0 L w →
    (∀ {tenv : Lean.Environment} (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst)) →
    RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      mctx mref cctx cref w (M, D) w' →
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4 ∧
      J L 1 w3 ∧ J L 1 w4 ∧ J L 1 w'
-- I3c balance: symbolic flag replaced by the default flags (`[] false`)
#mutant_rejected core_symbolic_balance :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (declName : Name)
    (parameters : List (String × Nat)) {w : Void IO.RealWorld},
    StartV L w → L.quiet w → L.dval w = 0 →
    Out0 L (endW mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName [] false true) w) ∧
    ErrOk mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName [] false true) w
-- I3c keeps: depth D+1 instead of D at the conclusion
#mutant_rejected core_symbolic_keeps :
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (L : RefLaws mref cref) (D : Nat) (declName : Name)
    (parameters : List (String × Nat)) (_hA0 : D = 0 → L.aux {}),
    (∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst)) →
    Keeps mctx mref cctx cref (J L (D + 1))
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
-- legality: conclusion on a different design
#mutant_rejected specializeDesign_ok_legal :
  ∀ {design D' : Design} {θ : List (String × Nat)},
    Sparkle.IR.Specialize.specializeDesign design θ = .ok D' → LegalBinding D' θ

/-! ## 3. AXIOMS and 4. CLOSURE -/
#audit_axioms synthesizeCombinationalWithParameters_designTop
#audit_axioms specializeDesign_ok_legal
#audit_axioms body_symbolic_keeps
#audit_axioms core_symbolic_keeps
#audit_axioms core_symbolic_worlds
#audit_axioms core_symbolic_balance
#audit_axioms core_symbolic_triple0
#audit_axioms CombTopRunN
#audit_axioms LegalBinding
#audit_axioms ParamTopShips
#audit_axioms SpecSuccessAllPositive
#audit_axioms PostTransfer
#audit_closure synthesizeCombinationalWithParameters_designTop
#audit_closure specializeDesign_ok_legal
#audit_closure body_symbolic_keeps
#audit_closure core_symbolic_keeps
#audit_closure core_symbolic_worlds
#audit_closure core_symbolic_balance
#audit_closure core_symbolic_triple0
#audit_closure CombTopRunN
#audit_closure LegalBinding
#audit_closure ParamTopShips
#audit_closure SpecSuccessAllPositive
#audit_closure PostTransfer

/-! ## 5. CLOSURE detector fixtures (Check-only namespace; same detector as production, fixture forbidden name) -/
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

end Tests.Gen4.ParamIfaceCheck
