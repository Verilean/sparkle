import Lean
import Tools.ShippingGen4FPost
set_option autoImplicit false
-- Check of Tools/ShippingGen4FPost.lean against scripts/gen4/FPOST_FREEZE.md §2. Silent on success.
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


#type_beq Tools.ShippingGen4FPost.dropZW_parameters :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).parameters = m.parameters
#type_beq Tools.ShippingGen4FPost.mergeDuplicates_parameters :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.RegDedup.mergeDuplicates m).parameters = m.parameters
#type_beq Tools.ShippingGen4FPost.mergeDuplicates_name :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.RegDedup.mergeDuplicates m).name = m.name
#type_beq Tools.ShippingGen4FPost.mergeChecked_parameters :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.RefineCheck.mergeChecked m).parameters = m.parameters
#type_beq Tools.ShippingGen4FPost.topMap_keys :
  ∀ (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (N : String), (∀ x, (f x).name = x.name) → (∀ x, (f x).parameters = x.parameters) →
    ∀ (l : List Sparkle.IR.AST.Module),
    (l.map fun x => if x.name == N then f x else x).map (·.parameters) = l.map (·.parameters) ∧
    (l.map fun x => if x.name == N then f x else x).map (·.name) = l.map (·.name)

open Lean Sparkle.Compiler.Elab Tools.ShippingEntrySoundness in
#type_beq Tools.ShippingGen4FPost.fpost_run :
  ∀ {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design},
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (M', D') w' →
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName parameters true true)
        mctx mref cctx cref w (M, D) w1 ∧
      M'.parameters = M.parameters ∧ M'.name = M.name ∧
      D'.modules.map (·.parameters) = D.modules.map (·.parameters) ∧
      D'.modules.map (·.name) = D.modules.map (·.name)

-- mutants
#mutant_rejected Tools.ShippingGen4FPost.dropZW_parameters :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).parameters = []
#mutant_rejected Tools.ShippingGen4FPost.mergeChecked_parameters :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.RefineCheck.mergeChecked m).parameters = m.parameters.reverse
#mutant_rejected Tools.ShippingGen4FPost.mergeDuplicates_name :
  ∀ (m : Sparkle.IR.AST.Module), (Sparkle.IR.RegDedup.mergeDuplicates m).name = ""
#mutant_rejected Tools.ShippingGen4FPost.topMap_keys :
  ∀ (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (N : String), (∀ x, (f x).name = x.name) →
    ∀ (l : List Sparkle.IR.AST.Module),
    (l.map fun x => if x.name == N then f x else x).map (·.parameters) = l.map (·.parameters) ∧
    (l.map fun x => if x.name == N then f x else x).map (·.name) = l.map (·.name)

#audit_axioms Tools.ShippingGen4FPost.dropZW_parameters
#audit_axioms Tools.ShippingGen4FPost.mergeDuplicates_parameters
#audit_axioms Tools.ShippingGen4FPost.mergeDuplicates_name
#audit_axioms Tools.ShippingGen4FPost.mergeChecked_parameters
#audit_axioms Tools.ShippingGen4FPost.topMap_keys
#audit_axioms Tools.ShippingGen4FPost.fpost_run
#print axioms Tools.ShippingGen4FPost.fpost_run
