import Tools.ShippingMachineSeqLinkedR

/-! # (emptied) The three wired heads over `MachineRan`

This file held `machine_traceL_of_loop_causalRA_ran`, `_of_comb_callsRA_ran`
and `_of_data_causalRA_ran` (namespace `Tools.ShippingMachineCausal`) as
COPIES of the three built heads (round par/g-1). By the ruling of 2026-10-14
(second message, item 4) the heads are now split IN PLACE in
`Tools/ShippingMachineSeqLinkedR.lean`: the proofs are in the `_ran` forms
there, under the SAME full names, and each built head is the corollary at
`Tools.ShippingMachineRan.machineRan_of_closes`
(`docs/parallel/L-threading-split.md`, `scripts/ran_threading_split.py`).

NOTHING is declared here any more. The file is kept, import-only, because
`lakefile.lean` names it as a library root and two files import it
(`Tools/ShippingOutermostCommand.lean`, `Tests/Compiler/RanSplitStatementsTest.lean`).
It can be deleted together with its `lean_lib` entry and those two import
lines. -/
