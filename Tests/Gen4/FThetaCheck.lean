import Lean
import Tools.ShippingGen4FTheta
set_option autoImplicit false
-- Check of Tools/ShippingGen4FTheta.lean against scripts/gen4/FTHETA_FREEZE.md §2. Silent on success.
-- TYPE comparison is structural `Expr ==` (alpha-equivalence; binder names/infos are not compared) on the
-- instantiated elaborated expected type. Mutants are rejections by that comparison, not semantic counterexamples.

open Lean Elab Command Meta Sparkle.Compiler.Elab Tools.ShippingEntrySoundness Tools.ShippingLegacySem
open Tools.ShippingGen4FTheta

def elabTm (t : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def elabTy (t : Syntax) : TermElabM Expr := do
  let ty ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars ty

elab "#type_struct " c:ident " : " t:term : command => liftTermElabM do
  let ty ← elabTy t
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  unless info.type == ty do throwError "TYPE mismatch for {n}"

elab "#mutant_rejected " c:ident " : " t:term : command => liftTermElabM do
  let ty ← elabTy t
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  if info.type == ty then throwError "mutant NOT rejected for {n}"

elab "#value_struct " c:ident " := " t:term : command => liftTermElabM do
  let v ← elabTm t
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  unless info.value? == some v do throwError "VALUE mismatch for {n}"

elab "#mutant_value_rejected " c:ident " := " t:term : command => liftTermElabM do
  let v ← elabTm t
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  if info.value? == some v then throwError "value mutant NOT rejected for {n}"

elab "#audit_axioms " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let axs ← collectAxioms n
  let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless bad.isEmpty do throwError "{n}: axioms {bad}"

/-! ## 1. The frozen statement -/
#type_struct fTheta_natBinder : ∀ {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    (∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (fun _ _ _ => True)) →
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∀ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x

-- `NatBinderAt` is the unfolded clause of the freeze (so the type above is the frozen text).
#value_struct NatBinderAt := fun (mctx : Meta.Context) (nm : String) (x : Lean.Expr) =>
  ∃ (decl : LocalDecl) (t : Lean.Expr),
    MRunsIn x.fvarId!.getDecl mctx decl ∧ decl.userName.toString = nm ∧
    MRunsIn (Meta.whnf decl.type) mctx t ∧ t.isConstOf ``Nat = true

/-! ## 2. Mutants of the type (all well-typed, all must differ) -/
-- symbolicMode flipped to false
#mutant_rejected fTheta_natBinder : ∀ {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    (∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (fun _ _ _ => True)) →
    MReturns (synthesizeFromConst translate logProf declName parameters false cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∀ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x
-- conclusion without the run premise's world: the telescope premise dropped
#mutant_rejected fTheta_natBinder : ∀ {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∀ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x
-- "some" parameter instead of "every" parameter
#mutant_rejected fTheta_natBinder : ∀ {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    (∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (fun _ _ _ => True)) →
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∃ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x
-- type test dropped from the clause (any binder named p)
#mutant_value_rejected NatBinderAt := fun (mctx : Meta.Context) (nm : String) (x : Lean.Expr) =>
  ∃ (decl : LocalDecl),
    MRunsIn x.fvarId!.getDecl mctx decl ∧ decl.userName.toString = nm
-- name test replaced by a constant
#mutant_value_rejected NatBinderAt := fun (mctx : Meta.Context) (nm : String) (x : Lean.Expr) =>
  ∃ (decl : LocalDecl) (t : Lean.Expr),
    MRunsIn x.fvarId!.getDecl mctx decl ∧ decl.userName.toString = "x" ∧
    MRunsIn (Meta.whnf decl.type) mctx t ∧ t.isConstOf ``Nat = true
-- Int instead of Nat
#mutant_value_rejected NatBinderAt := fun (mctx : Meta.Context) (nm : String) (x : Lean.Expr) =>
  ∃ (decl : LocalDecl) (t : Lean.Expr),
    MRunsIn x.fvarId!.getDecl mctx decl ∧ decl.userName.toString = nm ∧
    MRunsIn (Meta.whnf decl.type) mctx t ∧ t.isConstOf ``Int = true

/-! ## 3. Negative control for the comparator itself: a different constant's type is not accepted -/
#mutant_rejected fTheta_natBinder : True

/-! ## 4. Axioms (standard three only) -/
#audit_axioms fTheta_natBinder
#audit_axioms inner_list
#audit_axioms outer_list
#audit_axioms MRunsIn.throwError
#print axioms fTheta_natBinder
