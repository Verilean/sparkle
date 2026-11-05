import Tools.ShippingGenFGLedgerPremisesR
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # Check for `FGLedgerPremisesStmtR` (scripts/gen5/RK1_FREEZE.md)

(1) The statement of `FGLedgerPremisesStmtR` is the statement of `FGLedgerPremisesStmt` with exactly the `h_C_RK1` binder removed:
both telescopes are walked together, the old one skipping `h_C_RK1`, and every binder name, binder info, binder type and the
conclusion are compared by `==` (after instantiating with the same free variables). A negative control: the same walk WITHOUT the skip
fails. (2) `readKeeps_of_cellPrem` and `fgLedgerPremisesStmtR_iff` against Expected. (3) Axioms.
Not claimed: a proof of FG, a supply of C.EN-4, whether C.EN-4 is TRUSTED. -/

namespace Tests.Gen5.FGLedgerPremisesRCheck
open Lean Meta
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tools.ShippingGenFGLedgerPremises

partial def walk (skip : Option Name) (a e : Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | _, .forallE ne te be bie =>
    if skip == some ne.eraseMacroScopes then
      -- the skipped binder must not occur in the rest of the old statement
      if be.hasLooseBVars then throwError "RK1 CHECK FAILED: the removed binder {ne} is used later"
      walk skip a (be.instantiate1 (mkConst ``True)) i
    else
      match a with
      | .forallE na ta ba bia =>
        unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "RK1 CHECK FAILED: binder {i} name {na} vs {ne}"
        unless bia == bie do throwError "RK1 CHECK FAILED: binder {i} info"
        unless ta == te do throwError "RK1 CHECK FAILED: binder {i} ({na}) type"
        withLocalDecl na bia ta fun x => walk skip (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
      | _ => throwError "RK1 CHECK FAILED: missing binder {i} ({ne})"
  | .forallE na .., _ => throwError "RK1 CHECK FAILED: extra binder {i} ({na})"
  | _, _ => unless a == e do throwError "RK1 CHECK FAILED: conclusion"

run_cmd Lean.Elab.Command.liftTermElabM do
  let a ← stmtOf ``FGLedgerPremisesStmtR
  let e ← stmtOf ``FGLedgerPremisesStmt
  walk (some `h_C_RK1) a e
  logInfo "RK1 BINDERS: FGLedgerPremisesStmtR = FGLedgerPremisesStmt minus h_C_RK1 (names, infos, types, conclusion by ==)"
  let ok ← try walk none a e; pure true catch _ => pure false
  if ok then throwError "RK1 CHECK CONTROL: walk without the skip accepted"
  let ok2 ← try walk (some `h_C_EN4) a e; pure true catch _ => pure false
  if ok2 then throwError "RK1 CHECK CONTROL: skipping h_C_EN4 accepted"
  logInfo "RK1 CONTROL: walk without the skip, and with h_C_EN4 skipped instead, are rejected"

def ExpReadKeeps : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (h : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref),
    Tools.ShippingStRefCorrespondence.ReadKeeps cref
def ExpIff : Prop := FGLedgerPremisesStmtR ↔ FGLedgerPremisesStmt

run_cmd Lean.Elab.Command.liftTermElabM do
  for (t, x) in [(``readKeeps_of_cellPrem, ``ExpReadKeeps), (``fgLedgerPremisesStmtR_iff, ``ExpIff)] do
    let a ← stmtOf t
    let b ← stmtOf x
    unless a == b do throwError "RK1 TYPE FAILED {t}"
    logInfo m!"RK1 TYPE OK {t}"
  for n in [``readKeeps_of_cellPrem, ``fgLedgerPremisesStmtR_iff] do
    checkAxioms n
  logInfo "RK1 COUNTS: BINDERS 1 (+2 controls), TYPE 2, AXIOMS 2"

end Tests.Gen5.FGLedgerPremisesRCheck
