import Tools.ShippingGen5ReaderTraceFinalB1
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- No sorry / axiom / native_decide.

/-! # Check for `readerTrace_final_b1` (scripts/gen5/CV56_FREEZE.md)

(1) BINDERS: the telescope of `readerTrace_final_b1` equals the telescope of `readerTrace_final` binder by binder (names, binder infos,
types by `==`); the conclusion is `C ∧ B1` where `C` is `readerTrace_final`'s conclusion (by `==`) and `B1` is the GenWF row b1.
(2) The names of the removed rows (`hcb` = C.CV-6, `hsp hss hls hn` = C.CV-5) are not binders of either theorem. (3) Negative controls:
the walk against `rowB1_of_dataE` (different telescope) fails, and a conclusion compare against `C` alone fails. (4) Axioms.
Not claimed: a GenWF assembly, a supply of `readerTrace_final`'s assumptions, FG. -/

namespace Tests.Gen5.ReaderTraceFinalB1Check
open Lean Meta
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)

/-- Walks two telescopes together; returns the two conclusions. -/
partial def walk (a e : Expr) (i : Nat := 0) (names : Array Name := #[]) : MetaM (Expr × Expr × Array Name) := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "B1 CHECK FAILED: binder {i} name {na} vs {ne}"
    unless bia == bie do throwError "B1 CHECK FAILED: binder {i} info"
    unless ta == te do throwError "B1 CHECK FAILED: binder {i} ({na}) type"
    withLocalDecl na bia ta fun x => walk (ba.instantiate1 x) (be.instantiate1 x) (i + 1) (names.push na.eraseMacroScopes)
  | .forallE na .., _ => throwError "B1 CHECK FAILED: extra binder {i} ({na})"
  | _, .forallE ne .. => throwError "B1 CHECK FAILED: missing binder {i} ({ne})"
  | _, _ => pure (a, e, names)

run_cmd Lean.Elab.Command.liftTermElabM do
  let a ← stmtOf ``Tools.ShippingGen5ReaderTraceFinalB1.readerTrace_final_b1
  let e ← stmtOf ``Tools.ShippingGen5ReaderTraceFinal.readerTrace_final
  -- walk inside one MetaM context so the conclusions share the free variables
  let ok ← forallTelescope e fun xs ce => do
    let a' ← instantiateForall a xs
    let some (lhs, _) := a'.and? | throwError "B1 CHECK FAILED: conclusion is not a conjunction"
    unless lhs == ce do throwError "B1 CHECK FAILED: first conjunct is not readerTrace_final's conclusion"
    if a' == ce then throwError "B1 CHECK CONTROL: conclusion equal to the root's alone"
    pure xs.size
  let (_, _, names) ← walk a e
  for n in [`hcb, `hsp, `hss, `hls, `hn] do
    if names.contains n then throwError "B1 CHECK FAILED: removed premise {n} is a binder"
  logInfo m!"B1 BINDERS: readerTrace_final_b1 has the {ok} binders of readerTrace_final ({names.toList}); conclusion = root's ∧ GenWF b1; no hcb / hsp / hss / hls / hn"
  let bad ← try let _ ← walk a (← stmtOf ``Tools.ShippingGen5Cover3R.rowB1_of_dataE); pure true catch _ => pure false
  if bad then throwError "B1 CHECK CONTROL: walk against rowB1_of_dataE accepted"
  logInfo "B1 CONTROL: walk against rowB1_of_dataE rejected"
  checkAxioms ``Tools.ShippingGen5ReaderTraceFinalB1.readerTrace_final_b1
  logInfo "B1 COUNTS: BINDERS 1 (+ conclusion compare + 2 controls), AXIOMS 1"

end Tests.Gen5.ReaderTraceFinalB1Check
