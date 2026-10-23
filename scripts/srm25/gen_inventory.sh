#!/bin/bash
# Machine part of G5_INVENTORY.txt (run from worktree root): verbatim definitions + file:line of every cited fact.
echo "=== G5 PROP (verbatim) ==="
awk '/^def ShippedRegsAreSlots/{p=1} p{print FILENAME":"FNR": "$0} /^$/{p=0}' Tools/ShippingSrm22Width.lean
echo "=== closeMachine / registers (verbatim) ==="
grep -n "^def registers" -A5 Sparkle/IR/Machine.lean | sed 's/^/Sparkle\/IR\/Machine.lean:/'
grep -n "^def closeMachine" -A18 Sparkle/IR/Machine.lean | sed 's/^/Sparkle\/IR\/Machine.lean:/'
echo "=== refineCheck init clause (verbatim) ==="
grep -n "rm.2.2.2.2 == ro.2.2.2.2" -B6 -A2 Sparkle/IR/RefineCheck.lean | sed 's/^/Sparkle\/IR\/RefineCheck.lean:/'
echo "=== CloseCalls ==="
grep -n "^def CloseCalls" -A8 Tools/ShippingMachineEntry.lean | sed 's/^/Tools\/ShippingMachineEntry.lean:/'
echo "=== producer: regs := ps.map Port.name ==="
grep -n "refine ⟨ps.map Port.name" Tools/ShippingMachineEntry.lean | sed 's/^/Tools\/ShippingMachineEntry.lean:/'
echo "=== CITED LEMMAS (file:line) ==="
for n in refineCheck_regWidth registers_mem closeMachine_body closeMachine_parts closedBody_kinds_of_run core_kids_facts core_kids_facts_ranAM core_raw_facts_ranAM \
  machine_ref_traceX machine_traceX shippedRegsFromSource_of_hierGate regsAtInit_of_hinit mem_seqRegs_openFlat regOf_some checkedOptimize_binding checkedOptimize_not_binding \
  synthesizeMachineCertified_soundX synthesizeMachineCertified_returns composedGW_of_T machine_linkedT_callsRGW core_hierGate_anyAM; do
  grep -rn "^theorem $n\b" --include=*.lean Tools Sparkle Tests | head -2 | sed "s/^/LEMMA $n: /" | cut -c1-200
done
for n in MachineWired MachinePreserves MachinePreservesX MachineTraceLBX ComposedGW ComposedG; do
  grep -rn "^def $n\b" --include=*.lean Tools Sparkle Tests | head -1 | sed "s/^/DEF $n: /" | cut -c1-200
done
