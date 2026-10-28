import Tests.Compiler.SeqDeepGrandEndpointAuditTest
import Tools.ShippingSeqParentGenD2
-- BUILT (unit SR3t): g3 exit 0 (generator on grand; audit and statement comparison inside).
-- SCOPE (binding): `#machine_seq_parent_endpoint grand` now GENERATES (depth-2 path of `Tools/ShippingSeqParentGenD2.lean`) the endpoint
-- `grand.epD2_endpoint` for the chain `grand -> mid -> cnt` (class: header of that file).  Asserted here: its type is `isDefEq` to the
-- hand-assembled SR3s endpoint `grand_noShips_noBdA_dcH`, and its whole conclusion is `isDefEq` to the explicit `GrandConcl 2 1`
-- (shared binders as the same free variables; altered terms rejected).  The generator's own audit ran inside the command (standard
-- axioms, outer premises = hr / entry / closes : True, forbidden old-boundary names absent, BndAg-like boundary in the conclusion with
-- `MachineDefines` for exactly the child and the grandchild).  NOT a general theorem: the boundary premises (O, T, AdmCtx, MachineDefines
-- mid / cnt, start world, cache) stay inside `grand.epD2_Bnd`; RealChildA is a history of past synthesis results; `T` is an ADDED boundary.
namespace Tests.Compiler.SeqDeepGenTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Lean Meta Elab Command

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand

-- the call structure of the root, read by KERNEL-checked equations: root -> child -> leaf
theorem grand_callees : grand.machineData.shape.insts.map (·.1) = [``mid, ``mid] := by decide
theorem mid_callees : mid.machineData.shape.insts.map (·.1) = [``cnt, ``cnt] := by decide
theorem cnt_callees : cnt.machineData.shape.insts.map (·.1) = [] := by decide

#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.epD2_endpoint

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let gen := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.epD2_endpoint
  let hand := `Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH
  let gt := (← getConstInfo gen).type
  let ht := (← getConstInfo hand).type
  unless ← isDefEq gt ht do throwError "SR3t AUDIT FAILED: the generated grand endpoint differs from the hand-assembled grand_noShips_noBdA_dcH"
  forallTelescope gt fun xs concl => do
    unless xs.size == 11 do throwError "SR3t AUDIT FAILED: the endpoint has {xs.size} binders, expected 11"
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry", "closes"] do
      throwError "SR3t AUDIT FAILED: endpoint binder names are {names}"
    let mk (n kD : Nat) : Lean.Expr :=
      mkAppN (mkConst ``Tests.Compiler.SeqDeepGrandEndpointAuditTest.GrandConcl)
        #[mkNatLit n, mkNatLit kD, xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[6]!, xs[7]!]
    let exp := mk 2 1
    let concl ← instantiateMVars concl
    for (e, what) in [(concl, "the endpoint's conclusion"), (exp, "the expected conclusion")] do
      if e.hasMVar then throwError "SR3t AUDIT FAILED: unassigned metavariables in {what}"
      for f in (Lean.collectFVars {} e).fvarIds do
        unless xs.any (·.fvarId! == f) do throwError "SR3t AUDIT FAILED: out-of-scope free variable in {what}"
    Meta.check exp
    unless (← isDefEq concl exp) do
      throwError "SR3t AUDIT FAILED: the conclusion of the generated endpoint is not definitionally GrandConcl 2 1"
    for (n, kD) in [(1, 1), (2, 0)] do
      if (← isDefEq concl (mk n kD)) then throwError "SR3t AUDIT FAILED: the altered expected term GrandConcl {n} {kD} was ACCEPTED"
  logInfo m!"SR3t: the GENERATED grand.epD2_endpoint has a type isDefEq to the hand-assembled grand_noShips_noBdA_dcH, and its conclusion is isDefEq to GrandConcl 2 1 (GrandConcl 1 1 and GrandConcl 2 0 REJECTED)"

end Tests.Compiler.SeqDeepGenTest
