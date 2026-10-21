import Tests.Compiler.ParentSeqComposedATest
import Tools.ShippingSeqParentGen
-- UNBUILT (unit SR3i)
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
  unless ← isDefEq nt ht do throwError "generated parent endpoint differs from the hand-wired parent_noShips_noBdA_dcHL"
  logInfo m!"SR3i: the GENERATED parent endpoint has a type isDefEq to the hand-wired parent_noShips_noBdA_dcHL"

set_option maxHeartbeats 0 in
#machine_seq_parent_endpoint Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained

end Tests.Compiler.SeqParentGenTest
