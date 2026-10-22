import Tests.Compiler.TopShareComposedTest
import Tools.ShippingSeqParentGenD2MS
-- BUILT (unit SR13): s6 exit 0 (dev run); the final-SHA rebuild is in REPORT-SR13.md.
-- SCOPE (binding): the SHARED-leaf candidate `Tools/ShippingSeqParentGenD2MS.lean` applied to the ORIGINAL shared-leaf example `topshare`
-- (callees `wrap`, `wrap3`, leaf `acc`).  The old chain `#machine_design_svNR topshare 2` comes with the import of `TopShareComposedTest`.
-- The generated endpoint `topshare.epD2M_endpoint` is compared by `isDefEq` with the type of the hand-pasted `topshare_noShips_noBd_dc` of
-- `TopShareComposedTest` (the SR11/SR12 instance obtained by editing the template text by hand): the SAME statement up to the boundary definition
-- (`epD2M_Bnd` vs `ts_Bnd`, unfolded).  This is a cross-check of the candidate against the earlier hand-made instance, not a proof for further parents.
set_option sparkle.sharedLeafCandidate true in
#machine_seq_parent_endpoint Tests.Compiler.SeqDeepGenDiffTest.topshare

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let gen := ``Tests.Compiler.SeqDeepGenDiffTest.topshare.epD2M_endpoint
  let old := ``Tests.Compiler.TopShareComposedTest.topshare_noShips_noBd_dc
  let tg := (← getConstInfo gen).type
  let to := (← getConstInfo old).type
  unless (← isDefEq tg to) do throwError "SR13 CROSS-CHECK FAILED: the generated statement of {gen} differs from the hand-pasted {old}"
  logInfo m!"SR13 CROSS-CHECK: the statement of the GENERATED {gen} is isDefEq (default transparency) to the hand-pasted {old}"
