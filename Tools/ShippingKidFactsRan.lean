import Tools.ShippingKidFacts
import Tools.ShippingMachineRanBase

/-! # (emptied) The design-level chain of a parent with calls, over `MachineRan`

This file held the `_ran` SIBLINGS of fourteen threading theorems as COPIES of
their built originals (round par/g-1). By the ruling of 2026-10-14 (second
message, item 4) each original is now split IN PLACE: the proof is in
`<name>_ran` in the original's own file, under the SAME full name the copy
had here, and the original is its corollary at
`Tools.ShippingMachineRan.machineRan_of_closes`
(`docs/parallel/L-threading-split.md`, `scripts/ran_threading_split.py`):

| `_ran` form | now in |
|---|---|
| `Tools.ShippingChecksCoreGate.core_outsCheck_all_gate_ran` | `Tools/ShippingChecksCoreGate.lean` |
| `Tools.ShippingChecksWidths.core_hierGate_ran`, `core_callPorts_ran`, `core_instOutWidthsOk_ran` | `Tools/ShippingChecksWidths.lean` |
| `Tools.ShippingChecksRaw.core_raw_facts_ran` | `Tools/ShippingChecksRaw.lean` |
| `Tools.ShippingChecksRunFacts.core_runFacts_ran` | `Tools/ShippingChecksRunFacts.lean` |
| `Tools.ShippingPortsMatchRaw.core_portsMatch_raw_ran` | `Tools/ShippingPortsMatchRaw.lean` |
| `Tools.ShippingKidsSelf.core_kidsMaskedN_top_ran`, `core_kidsPass_deep_ran` | `Tools/ShippingKidsSelf.lean` |
| `Tools.ShippingTextShipped.core_designCheck_run_ran` | `Tools/ShippingTextShipped.lean` |
| `Tools.ShippingKidFacts.kids_runFacts_ran`, `kids_outsCheck_ran`, `kids_maskedN_ran`, `kids_designCheck_ran` | `Tools/ShippingKidFacts.lean` |

NOTHING is declared here any more. The file is kept, import-only, because
`lakefile.lean` names it as a library root and two files import it
(`Tools/ShippingOutermostCommand.lean`, `Tests/Compiler/RanSplitStatementsTest.lean`);
importing `Tools.ShippingKidFacts` gives every name above. It can be deleted
together with its `lean_lib` entry and those two import lines. -/
