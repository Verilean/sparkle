import Tests.Compiler.ParentSeqComposedATest
import Tests.Compiler.ShippingChildBoundaryTest
import Tools.ShippingSeqParentGen
import Tools.ShippingShipsFreeMaskedCommand
-- BUILT (unit SR3k): k6 exit 0 (`parent`, `chained`, and now `two` = two DIFFERENT children cnt/acc, GENERATED, with asserted call-position -> child -> data map).
-- BUILT (unit SR3i): see REPORT-SR3i.md for the run names / exits (build of Tests.Compiler.SeqParentGenTest). In-test audits THROW on failure.
-- SCOPE (binding): `#machine_seq_parent_endpoint f` (Tools/ShippingSeqParentGen.lean) GENERATES, for a declaration `f` of the class stated in that
-- file's header (non-memory parent; every call instance calls a generated sequential LEAF child — one or SEVERAL different child declarations since SR3k; depth n = 1, kD = number of the parent's own inputs),
-- the new-boundary design endpoint `f.epA_endpoint` with the same shape as the hand-wired `parent_noShips_noBdA_dcHL` of units SR3c-SR3h:
-- premises `hr`, `entry`, `closes : True`; `f.epA_Bnd` (existential over O / T : RefLawsATele / AdmCtx / MachineDefines child / JQ start world)
-- stays in the conclusion, NOT a proof that it holds.  Applied here to `parent` (type checked `isDefEq` to the hand-wired endpoint) and to
-- `chained` (the same child `cnt` called twice, the second call's argument another call's field) and (unit SR3k) `two` (two DIFFERENT children).  NOT unconditional semantic equivalence;
-- RealChildA is a history; T is an ADDED boundary; not runtime fit.
namespace Tests.Compiler.SeqParentGenTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let new := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.epA_endpoint
  let hand := ``Tests.Compiler.ParentSeqComposedATest.parent_noShips_noBdA_dcHL
  let nt := (← getConstInfo new).type
  let ht := (← getConstInfo hand).type
  unless ← isDefEq nt ht do throwError "SR3i AUDIT FAILED: generated parent endpoint differs from the hand-wired parent_noShips_noBdA_dcHL"
  logInfo m!"SR3i: the GENERATED parent endpoint has a type isDefEq to the hand-wired parent_noShips_noBdA_dcHL (its BndA is epA_Bnd unfolded)"

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained

-- unit SR3k: two DIFFERENT sequential children (`cnt` and `acc`): now GENERATED.  The old generator `#machine_design_svNR` provides the
-- reused pieces (and the old endpoint `two.machine_design_noShipsNoMaskedNR1`, against which the audit compares the conclusion).
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two 1

-- the OLD endpoint for `two` (the old command takes one `hR_j : MachineDefines` per distinct kid): generated so that the audit compares with it
set_option maxHeartbeats 0 in
#machine_no_ships_masked Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two 1

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two

-- (`two` has FOUR call instances: one per (call, used output field): cnt twice, acc twice)
theorem two_nm0 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 0 = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by decide
theorem two_nm1 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 1 = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by decide
theorem two_nm2 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 2 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by decide
theorem two_nm3 : Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_nm 3 = ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc := by decide

-- the call position -> child declaration -> that child's data map of `two`, ASSERTED (the second call's data come from `acc`, not `cnt`)
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let two := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two
  let cnt := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let acc := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
  -- position k ↦ callee: KERNEL-checked theorems below (`two_nm0`, `two_nm1`); here the instance list is also read back
  let callees ← Tools.ShippingSeqParentGen.readNames
    (← Tools.ShippingSeqParentGen.elabText s!"({two}.machineData.shape.insts.map (·.1))")
  unless callees == [cnt, cnt, acc, acc] do throwError "SR3k AUDIT FAILED: call positions of `two` map to {callees}, expected [cnt, cnt, acc, acc]"
  -- the generated key tables at position k are the data of THAT child: `epA_K_j` (the proved equation for child j) mentions
  -- only child j's `epA_nk` / `machineData`, never the other child's
  let mut seen : Array String := #[]
  for (j, c, other) in [(0, cnt, acc), (1, acc, cnt)] do
    let ty := (← getConstInfo (two ++ Name.mkSimple s!"epA_K_{j}")).type
    unless (ty.find? (·.isConstOf (c ++ `epA_nk))).isSome && (ty.find? (·.isConstOf (c ++ `machineData))).isSome do
      throwError "SR3k AUDIT FAILED: epA_K_{j} does not mention the data of {c}"
    if (ty.find? (·.isConstOf (other ++ `epA_nk))).isSome || (ty.find? (·.isConstOf (other ++ `machineData))).isSome then
      throwError "SR3k AUDIT FAILED: epA_K_{j} mentions the data of {other}"
    seen := seen.push s!"child {j} = {c}: epA_K_{j} mentions exactly {c}'s epA_nk / machineData"
  -- the boundary: one `MachineDefines` per distinct child, and both children's `MachineDefines` arguments in the epA_closes hypotheses
  let cl := (← getConstInfo (two ++ `epA_closes)).type
  let hyps ← forallTelescope cl fun xs _ => xs.filterMapM fun x => do
    let t ← inferType x
    if t.getAppFn.isConstOf ``Tools.ShippingMachineEntry.MachineDefines then return some (← ppExpr t).pretty else return none
  unless hyps.size == 2 && (hyps.any fun s => (s.splitOn "cnt").length > 1) && (hyps.any fun s => (s.splitOn "acc").length > 1) do
    throwError "SR3k AUDIT FAILED: epA_closes should ask MachineDefines for exactly cnt and acc, found {hyps}"
  logInfo m!"SR3k: `two` call positions -> children {callees}; {seen}; epA_closes asks exactly one MachineDefines per distinct child: {hyps}. (`chained` repeats ONE child: a single MachineDefines, shared child data; `two` has one per DIFFERENT child.)"

#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.epA_endpoint
#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.epA_endpoint
#print axioms Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two.epA_endpoint

end Tests.Compiler.SeqParentGenTest
