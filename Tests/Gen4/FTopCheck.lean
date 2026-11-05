import Lean
import Tools.ShippingGen4FTop
set_option autoImplicit false
-- Check of Tools/ShippingGen4FTop.lean against scripts/gen4/FTOP_FREEZE.md §2. Silent on success.
-- TYPE comparison is structural `Expr ==` (alpha-equivalence; binder names/infos are not compared) on the
-- instantiated elaborated expected type. Mutants are rejections by that comparison, not semantic counterexamples.

open Lean Elab Command Meta Sparkle.Compiler.Elab Tools.ShippingEntrySoundness Tools.ShippingLegacySem
open Sparkle.IR.Builder Tools.ShippingGen4FTop

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

/-! ## 1. The frozen statements -/
#type_struct fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
#type_struct fTop_out : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    Sparkle.IR.ModuleNameCheck.check (M :: D.modules) = true ∧
    (∀ p ∈ parameters, ∃ q ∈ M.parameters, q.name = p.1) ∧
    SeqFree M

-- `SeqFree` is the unfolded symbolic-mode body test of the freeze (matcher constants differ, so by `rfl`, not `==`).
example (m : Sparkle.IR.AST.Module) : SeqFree m =
    ((m.body.any fun stmt => match stmt with
      | .register .. | .memory .. | .inst .. => true
      | _ => false) = false) := rfl

/-! ## 2. Mutants of the type (all well-typed, all must differ) -/
-- symbolicMode flipped
#mutant_rejected fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters false cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
-- name check dropped
#mutant_rejected fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
-- name check on the design modules alone
#mutant_rejected fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check fcs.design.modules = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
-- some parameter instead of every
#mutant_rejected fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∃ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
-- D = fcs.design dropped
#mutant_rejected fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
-- M = fcs.module (no finalize)
#mutant_rejected fTop_finish : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    ∃ fcs : CircuitState,
      M = fcs.module ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module
-- symbolicMode flipped
#mutant_rejected fTop_out : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters false cfe
      (.defnInfo dv) isInst) (M, D) →
    Sparkle.IR.ModuleNameCheck.check (M :: D.modules) = true ∧
    (∀ p ∈ parameters, ∃ q ∈ M.parameters, q.name = p.1) ∧
    SeqFree M
-- check on D.modules alone
#mutant_rejected fTop_out : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    Sparkle.IR.ModuleNameCheck.check D.modules = true ∧
    (∀ p ∈ parameters, ∃ q ∈ M.parameters, q.name = p.1) ∧
    SeqFree M
-- coverage on the wrong direction
#mutant_rejected fTop_out : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    Sparkle.IR.ModuleNameCheck.check (M :: D.modules) = true ∧
    (∀ q ∈ M.parameters, ∃ p ∈ parameters, q.name = p.1) ∧
    SeqFree M
-- SeqFree dropped
#mutant_rejected fTop_out : ∀ (_htel : Tools.ShippingLegacySem.LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design},
    MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D) →
    Sparkle.IR.ModuleNameCheck.check (M :: D.modules) = true ∧
    (∀ p ∈ parameters, ∃ q ∈ M.parameters, q.name = p.1)
/-! ## 3. Negative controls -/
-- comparator: a different statement is not accepted
#mutant_rejected fTop_finish : True
-- FTOP_FREEZE §4: `check` does NOT exclude two modules with the same name, so the
-- `∀ x ∈ D.modules, x.name ≠ M.name` guard is not a consequence of the name check.
theorem check_dup_name (m : Sparkle.IR.AST.Module) (h : m.body = []) :
    Sparkle.IR.ModuleNameCheck.check [m, m] = Sparkle.IR.ModuleNameCheck.check [m] := by
  simp [Sparkle.IR.ModuleNameCheck.check, Sparkle.IR.ModuleNameCheck.namesOf, h, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

-- so: whenever a body-free module passes `check` alone, the pair [m, m] passes, and the guard fails on it
example (m : Sparkle.IR.AST.Module) (h : m.body = [])
    (hc : Sparkle.IR.ModuleNameCheck.check [m] = true) :
    Sparkle.IR.ModuleNameCheck.check ([m] ++ [m]) = true ∧ ¬ (∀ x ∈ [m], x.name ≠ m.name) :=
  ⟨by simpa [check_dup_name m h] using hc, fun hg => hg m (by simp) rfl⟩

/-! ## 4. Axioms (standard three only) -/
#audit_axioms fTop_finish
#audit_axioms fTop_out
#audit_axioms seqFree_filterMap
#audit_axioms namesOf_seqFree
#audit_axioms namesOf_finalize
#print axioms fTop_finish
#print axioms fTop_out
