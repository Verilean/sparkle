import Tests.Compiler.ParentSeqComposedATest
import Tests.Compiler.ShippingChildBoundaryTest
import Tools.ShippingSeqParentGen
-- BUILT (unit SR3i): see REPORT-SR3i.md for the run names / exits (build of Tests.Compiler.SeqParentGenTest). In-test audits THROW on failure.
-- SCOPE (binding): `#machine_seq_parent_endpoint f` (Tools/ShippingSeqParentGen.lean) GENERATES, for a declaration `f` of the class stated in that
-- file's header (non-memory parent; every call instance calls ONE sequential leaf child; depth n = 1, kD = number of the parent's own inputs),
-- the new-boundary design endpoint `f.epA_endpoint` with the same shape as the hand-wired `parent_noShips_noBdA_dcHL` of units SR3c-SR3h:
-- premises `hr`, `entry`, `closes : True`; `f.epA_Bnd` (existential over O / T : RefLawsATele / AdmCtx / MachineDefines child / JQ start world)
-- stays in the conclusion, NOT a proof that it holds.  Applied here to `parent` (type checked `isDefEq` to the hand-wired endpoint) and to
-- `chained` (the same child `cnt` called twice, the second call's argument another call's field).  NOT unconditional semantic equivalence;
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

-- outside the class: two DIFFERENT sequential children (`cnt` and `acc`): the command REFUSES TO GENERATE and says why; nothing is narrowed
open Lean Elab Command in
run_cmd do
  let msgs0 := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand (← `(#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two))
  let ms := (← get).messages
  modify fun s => { s with messages := msgs0 }
  unless ms.hasErrors do throwError "SR3i AUDIT FAILED: `two` was accepted"
  let txt ← ms.toList.foldlM (fun acc m => do return acc ++ (← m.toString)) ""
  unless (txt.splitOn "ONE child declaration").length > 1 do
    throwError "SR3i AUDIT FAILED: unexpected refusal message {txt}"
  logInfo m!"SR3i: `two` (two different children) is outside the class and is reported as such (nothing generated): {txt}"

#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.epA_endpoint
#print axioms Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.epA_endpoint

end Tests.Compiler.SeqParentGenTest
