import Tools.ShippingGen4ParamEntry
set_option autoImplicit false
-- Built in g4par-impl e2d16d19 (clean, exit 0, 253 jobs): TYPE 9, MUTANT 5 signature/defeq rejections, AXIOMS 9, CLOSURE 9.

/-! # Audit of Tools/ShippingGen4ParamEntry.lean (scripts/gen4/PARAMETRIC_FREEZE.md rev3 §9.1)

1. TYPE: each theorem's type is `isDefEq` to an independent copy of the frozen statement (written here from the freeze).
2. MUTANT: signature/defeq REJECTIONS only. A mutant type that is not defeq to the theorem's type is rejected; this is
   NOT a semantic counterexample and says nothing about whether the mutated statement is true.
3. AXIOMS: only propext / Classical.choice / Quot.sound; no sorryAx, no `ofReduceBool` (native_decide).
4. CLOSURE: the transitive constant closure of each theorem has no `Laws`, `T1Hyp`, `T1HypND` constant.
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

private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++ (match ci.value? with
        | some v => v.getUsedConstants.toList
        | none => [])
      closure env (cs ++ rest) seen

elab "#audit_closure " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let env ← getEnv
  let seen := closure env [n] {}
  let forbidden := [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]
  let bad := seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m
  unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"

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

end Tests.Gen4.ParamEntryCheck
