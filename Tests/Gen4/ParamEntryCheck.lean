import Tools.ShippingGen4ParamEntry
set_option autoImplicit false
-- Built in g4par-impl e2d16d19 (clean, exit 0, 253 jobs): TYPE 9, MUTANT 5 signature/defeq rejections, AXIOMS 9, CLOSURE 9.

/-! # Audit of Tools/ShippingGen4ParamEntry.lean (scripts/gen4/PARAMETRIC_FREEZE.md rev3 §9.1)

1. TYPE: each theorem's type is `isDefEq` to an independent copy of the frozen statement (written here from the freeze).
2. MUTANT: signature/defeq REJECTIONS only. A mutant type that is not defeq to the theorem's type is rejected; this is
   NOT a semantic counterexample and says nothing about whether the mutated statement is true.
3. AXIOMS: only propext / Classical.choice / Quot.sound; no sorryAx, no `ofReduceBool` (native_decide).
4. CLOSURE: the transitive constant closure of each theorem (types plus `thmInfo.value`/`defnInfo.value`; `opaque`
   bodies are not tracked and are logged) has no `Laws`, `T1Hyp`, `T1HypND` constant. Section 5 runs proof-only
   negative (direct, via other-namespace helper) and positive fixtures through the same detector.
Scope limits are those of the module docstring: I3b is a non-linked existence peel; I5a is a name-only map. -/

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

private def fixtureForbidden : List Name := [`Tests.Gen4.ParamEntryCheck.Fixture.Bad]

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

namespace Tests.Gen4.ParamEntryCheck
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingGen4ParamEntry

/-! ## 1. TYPE -/
#type_defeq certifiedShape_off :
  ∀ (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo),
    (symbolicMode || !parameters.isEmpty) = true → certifiedShape? symbolicMode parameters ci = none
#type_defeq mixedCertifiedShape_off :
  ∀ (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
    (symbolicMode || !parameters.isEmpty) = true → mixedCertifiedShape? symbolicMode parameters ci isInst = none
#type_defeq machineShape_off :
  ∀ (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv)
    (allowInsts : Bool), (symbolicMode || !parameters.isEmpty) = true →
    machineShape? symbolicMode parameters ci senv allowInsts = none
#type_defeq entryConst_off :
  ∀ (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (isInst : Lean.Expr → Bool) (inl : Lean.Expr → Lean.Expr) (projs : StructEnv),
    (symbolicMode || !parameters.isEmpty) = true →
    entryConst certifiedFrontEnd symbolicMode parameters ci isInst inl projs = ci
#type_defeq finishSynth_symbolic :
  ∀ {declName : Name} {parameters : List (String × Nat)} {fcs : CircuitState} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design},
    RunsTo (finishSynth declName parameters true fcs) mctx mref cctx cref w (M, D) w' →
    (fcs.module.body.any fun stmt => match stmt with
        | .register .. | .memory .. | .inst .. => true
        | _ => false) = false
    ∧ (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1)
    ∧ Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true
    ∧ M = fcs.module.finalize ∧ D = fcs.design
#type_defeq core_symbolic_prologue :
  ∀ {translate : Lean.Environment → TranslateFn} {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design},
    RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe) mctx mref cctx cref w (M, D) w' →
    dupParams parameters = false ∧ zeroParam parameters = false
#type_defeq core_symbolic_prologue_throws :
  ∀ {translate : Lean.Environment → TranslateFn} {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld},
    (dupParams parameters || zeroParam parameters) = true →
    ∀ (r : Sparkle.IR.AST.Module × Design) (w' : Void IO.RealWorld),
    ¬ RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe) mctx mref cctx cref w r w'
#type_defeq core_symbolic_reads :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design},
    RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true) mctx mref cctx cref w (M, D) w' →
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4
#type_defeq specializeDesign_ok_facts :
  ∀ {design D' : Design} {bindings : Sparkle.IR.Specialize.Bindings},
    Sparkle.IR.Specialize.specializeDesign design bindings = .ok D' →
    (design.findModule design.topModule).isSome = true
    ∧ D'.topModule = design.topModule
    ∧ D'.modules.map (·.name) = design.modules.map (·.name)
    ∧ (∀ m ∈ D'.modules, m.parameters = [])
    ∧ (∀ mn : String, (Sparkle.IR.Machine.moduleByName D'.modules mn).map (·.name)
          = (Sparkle.IR.Machine.moduleByName design.modules mn).map (·.name))
    ∧ (∀ mn : String, (Tools.ShippingMachineLinked.childMap D'.modules mn).map (fun c => c.1.name)
          = (Tools.ShippingMachineLinked.childMap design.modules mn).map (fun c => c.1.name))

/-! ## 2. MUTANT (signature/defeq rejections, NOT semantic counterexamples) -/
-- guard `&&` instead of `||`
#mutant_rejected certifiedShape_off :
  ∀ (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo),
    (symbolicMode && !parameters.isEmpty) = true → certifiedShape? symbolicMode parameters ci = none
-- I3a with `∨`
#mutant_rejected core_symbolic_prologue :
  ∀ {translate : Lean.Environment → TranslateFn} {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design},
    RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe) mctx mref cctx cref w (M, D) w' →
    dupParams parameters = false ∨ zeroParam parameters = false
-- I3b with `[] false` instead of the symbolic flags
#mutant_rejected core_symbolic_reads :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design},
    RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true) mctx mref cctx cref w (M, D) w' →
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName [] false true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4
-- I2 without the `D = fcs.design` conjunct
#mutant_rejected finishSynth_symbolic :
  ∀ {declName : Name} {parameters : List (String × Nat)} {fcs : CircuitState} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design},
    RunsTo (finishSynth declName parameters true fcs) mctx mref cctx cref w (M, D) w' →
    (fcs.module.body.any fun stmt => match stmt with
        | .register .. | .memory .. | .inst .. => true
        | _ => false) = false
    ∧ (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1)
    ∧ Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true
    ∧ M = fcs.module.finalize
-- I5a without the `topModule` conjunct
#mutant_rejected specializeDesign_ok_facts :
  ∀ {design D' : Design} {bindings : Sparkle.IR.Specialize.Bindings},
    Sparkle.IR.Specialize.specializeDesign design bindings = .ok D' →
    (design.findModule design.topModule).isSome = true
    ∧ D'.modules.map (·.name) = design.modules.map (·.name)
    ∧ (∀ m ∈ D'.modules, m.parameters = [])
    ∧ (∀ mn : String, (Sparkle.IR.Machine.moduleByName D'.modules mn).map (·.name)
          = (Sparkle.IR.Machine.moduleByName design.modules mn).map (·.name))
    ∧ (∀ mn : String, (Tools.ShippingMachineLinked.childMap D'.modules mn).map (fun c => c.1.name)
          = (Tools.ShippingMachineLinked.childMap design.modules mn).map (fun c => c.1.name))

/-! ## 3. AXIOMS and 4. CLOSURE -/
#audit_axioms certifiedShape_off
#audit_axioms mixedCertifiedShape_off
#audit_axioms machineShape_off
#audit_axioms entryConst_off
#audit_axioms finishSynth_symbolic
#audit_axioms core_symbolic_prologue
#audit_axioms core_symbolic_prologue_throws
#audit_axioms core_symbolic_reads
#audit_axioms specializeDesign_ok_facts
#audit_closure certifiedShape_off
#audit_closure mixedCertifiedShape_off
#audit_closure machineShape_off
#audit_closure entryConst_off
#audit_closure finishSynth_symbolic
#audit_closure core_symbolic_prologue
#audit_closure core_symbolic_prologue_throws
#audit_closure core_symbolic_reads
#audit_closure specializeDesign_ok_facts

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

end Tests.Gen4.ParamEntryCheck
