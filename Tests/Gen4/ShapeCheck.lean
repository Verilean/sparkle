import Lean
import Tools.ShippingGen4Shape
set_option autoImplicit false
-- Check of Tools/ShippingGen4Shape.lean against scripts/gen4/SHAPE_FREEZE.md §2. Silent on success.
-- TYPE checks are structural `Expr ==` (after elaboration and instantiateMVars), not strings.
-- Mutants are rejections by structural inequality, not semantic counterexamples.

open Lean Elab Command Meta
open Sparkle.IR.AST

private def elabTy (t : Syntax) : TermElabM Lean.Expr := do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars ty

elab "#type_beq " c:ident " : " t:term : command => liftTermElabM do
  let ty ← elabTy t
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  unless info.type == ty do throwError "TYPE mismatch for {n}"

elab "#mutant_rejected " c:ident " : " t:term : command => liftTermElabM do
  let ty ← elabTy t
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  if info.type == ty then throwError "mutant NOT rejected for {n}"

elab "#audit_axioms " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let axs ← collectAxioms n
  let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless bad.isEmpty do throwError "{n}: axioms {bad}"



private def elabVal (c : Ident) (t : Syntax) : TermElabM (Name × Lean.Expr × Lean.Expr) := do
  let v ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let v ← instantiateMVars v
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  let some val := info.value? | throwError "{n} has no value"
  pure (n, val, v)

elab "#value_beq " c:ident " : " t:term : command => liftTermElabM do
  let (n, val, v) ← elabVal c t
  unless val == v do throwError "VALUE mismatch for {n}"

elab "#value_mutant_rejected " c:ident " : " t:term : command => liftTermElabM do
  let (n, val, v) ← elabVal c t
  if val == v then throwError "value mutant NOT rejected for {n}"

open Tools.ShippingGen4Shape Tools.ShippingGen4ParamIface

-- the definition (design' of synthesizeHierarchicalWithParameters)
#value_beq Tools.ShippingGen4Shape.SpecDesign :
  fun (M : Sparkle.IR.AST.Module) (D : Design) =>
    if D.modules.any (·.name == M.name) then D else D.addModule M

#type_beq Tools.ShippingGen4Shape.legalBinding_congr :
  ∀ {D₁ D₂ : Design} {θ : List (String × Nat)},
    D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters) →
    D₁.modules.map (·.name) = D₂.modules.map (·.name) →
    (LegalBinding D₁ θ ↔ LegalBinding D₂ θ)

#type_beq Tools.ShippingGen4Shape.specDesign_eq_addModule :
  ∀ {M : Sparkle.IR.AST.Module} {D : Design},
    (∀ x ∈ D.modules, x.name ≠ M.name) → SpecDesign M D = D.addModule M

#type_beq Tools.ShippingGen4Shape.specDesign_keys :
  ∀ {M₁ M₂ : Sparkle.IR.AST.Module} {D₁ D₂ : Design},
    M₁.name = M₂.name → M₁.parameters = M₂.parameters →
    D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters) →
    D₁.modules.map (·.name) = D₂.modules.map (·.name) →
    (SpecDesign M₁ D₁).modules.map (·.parameters) = (SpecDesign M₂ D₂).modules.map (·.parameters) ∧
    (SpecDesign M₁ D₁).modules.map (·.name) = (SpecDesign M₂ D₂).modules.map (·.name)

open Lean Sparkle.Compiler.Elab Tools.ShippingEntrySoundness in
#type_beq Tools.ShippingGen4Shape.shape_run :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design},
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w' →
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      (SpecDesign M' D').topModule = D.topModule ∧
      (SpecDesign M' D').modules.map (·.parameters) = (SpecDesign M D).modules.map (·.parameters) ∧
      (SpecDesign M' D').modules.map (·.name) = (SpecDesign M D).modules.map (·.name) ∧
      (∀ θ, LegalBinding (SpecDesign M' D') θ ↔ LegalBinding (SpecDesign M D) θ) ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) →
        SpecDesign M' D' = D'.addModule M' ∧ SpecDesign M D = D.addModule M)

-- mutants / negative controls
#value_mutant_rejected Tools.ShippingGen4Shape.SpecDesign :
  fun (M : Sparkle.IR.AST.Module) (D : Design) =>
    if D.modules.any (·.name == M.name) then D.addModule M else D
#value_mutant_rejected Tools.ShippingGen4Shape.SpecDesign :
  fun (M : Sparkle.IR.AST.Module) (D : Design) => D.addModule M
#mutant_rejected Tools.ShippingGen4Shape.specDesign_eq_addModule :
  ∀ {M : Sparkle.IR.AST.Module} {D : Design}, SpecDesign M D = D.addModule M
#mutant_rejected Tools.ShippingGen4Shape.specDesign_eq_addModule :
  ∀ {M : Sparkle.IR.AST.Module} {D : Design},
    (∀ x ∈ D.modules, x.name ≠ M.name) → SpecDesign M D = D
#mutant_rejected Tools.ShippingGen4Shape.legalBinding_congr :
  ∀ {D₁ D₂ : Design} {θ : List (String × Nat)},
    D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters) →
    (LegalBinding D₁ θ ↔ LegalBinding D₂ θ)
#mutant_rejected Tools.ShippingGen4Shape.legalBinding_congr :
  ∀ {D₁ D₂ : Design} {θ : List (String × Nat)},
    D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters) →
    D₁.modules.map (·.name) = D₂.modules.map (·.name) →
    (LegalBinding D₁ θ → LegalBinding D₂ θ)
#mutant_rejected Tools.ShippingGen4Shape.specDesign_keys :
  ∀ {M₁ M₂ : Sparkle.IR.AST.Module} {D₁ D₂ : Design},
    M₁.name = M₂.name → M₁.parameters = M₂.parameters →
    D₁.modules.map (·.parameters) = D₂.modules.map (·.parameters) →
    (SpecDesign M₁ D₁).modules.map (·.parameters) = (SpecDesign M₂ D₂).modules.map (·.parameters) ∧
    (SpecDesign M₁ D₁).modules.map (·.name) = (SpecDesign M₂ D₂).modules.map (·.name)
-- the shape reads SpecDesign, not D'.addModule M' unconditionally
open Lean Sparkle.Compiler.Elab Tools.ShippingEntrySoundness in
#mutant_rejected Tools.ShippingGen4Shape.shape_run :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design},
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w' →
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      (D'.addModule M').topModule = D.topModule ∧
      (D'.addModule M').modules.map (·.parameters) = (D.addModule M).modules.map (·.parameters) ∧
      (D'.addModule M').modules.map (·.name) = (D.addModule M).modules.map (·.name) ∧
      (∀ θ, LegalBinding (D'.addModule M') θ ↔ LegalBinding (D.addModule M) θ) ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) →
        SpecDesign M' D' = D'.addModule M' ∧ SpecDesign M D = D.addModule M)

#audit_axioms Tools.ShippingGen4Shape.SpecDesign
#audit_axioms Tools.ShippingGen4Shape.legalBinding_congr
#audit_axioms Tools.ShippingGen4Shape.specDesign_eq_addModule
#audit_axioms Tools.ShippingGen4Shape.specDesign_keys
#audit_axioms Tools.ShippingGen4Shape.shape_run
