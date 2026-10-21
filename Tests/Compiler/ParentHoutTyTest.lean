import Tests.Compiler.ParentDesignCheckFATest
-- BUILT (unit SR3g, par/u-sr3g): g1 exit 0 (houtTy by decide). g2 (endpoint without houtTy + audit): see REPORT-SR3g.md.
-- SCOPE (binding): `houtTy` is PROVED for `parent` (decide on the concrete output list). soundL / composed (semantic part)
-- / hr / entry / closes and `BndA` (existential, not a proof that it holds) REMAIN premises. NOT unconditional semantic
-- equivalence; not runtime fit.
namespace Tests.Compiler.ParentHoutTyTest
open Sparkle.Compiler.Elab Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Lean Elab Command Meta Term
open Tests.Compiler.ChildVertAuditTest

/-- **`houtTy` for `parent`**: every output's type width equals its declared width (closed data, `decide`). -/
theorem parent_houtTy : ∀ o ∈ parent.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  stdAxioms ``parent_houtTy
  let ty := (← getConstInfo ``parent_houtTy).type
  let expTy := (← getConstInfo ``Tests.Compiler.ParentDesignCheckFATest.parent_noShips_noBdA_dc).type
  -- the dropped premise's statement is exactly `parent_houtTy`'s type
  let found ← forallTelescope expTy fun xs _ => do
    let mut r := false
    for x in xs do
      if (← x.fvarId!.getUserName) == `houtTy then
        r := r || (← isDefEq (← inferType x) ty)
    return r
  unless found do throwError "SR3g AUDIT FAILED: houtTy binder of parent_noShips_noBdA_dc is not parent_houtTy's type"
  logInfo m!"SR3g AUDIT OK: parent_houtTy has standard axioms and is defeq to the houtTy premise of parent_noShips_noBdA_dc"

#print axioms parent_houtTy
end Tests.Compiler.ParentHoutTyTest
