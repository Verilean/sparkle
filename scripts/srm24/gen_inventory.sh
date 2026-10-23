#!/bin/bash
# Machine part of G4_INVENTORY.txt (run from worktree root): verbatim G4 Prop, definitions and file:line of every cited lemma.
echo "=== G4 PROP TEXT (verbatim) ==="
awk '/^def ShippedRegWidthLe/{p=1} p{print FILENAME":"FNR": "$0} /^$/{p=0}' Tools/ShippingSrm22Width.lean
echo "=== DEFINITIONS (verbatim file:line) ==="
grep -n "^def declWidth" -A5 Sparkle/IR/RegDedup.lean | sed 's/^/Sparkle\/IR\/RegDedup.lean:/'
grep -n "^abbrev wofOf\|^abbrev weS" Tools/ShippingDesignSVLeaf.lean | sed 's/^/Tools\/ShippingDesignSVLeaf.lean:/'
grep -n "^def checkedOptimize" -A10 Sparkle/IR/RefineCheck.lean | sed 's/^/Sparkle\/IR\/RefineCheck.lean:/'
echo "=== CITED LEMMAS (file:line) ==="
for n in refineCheck_regWidth weS_checkedOptimize_le weOf_port checkedOptimize_ports checkedOptimize_ports_wires checkedOptimize_wires_subset \
  declWidth_of_wire declWidth_eq_weS wire_find moduleWof_wire core_closed_typedIn_ranAM core_hierGate_anyAM checkedOptimize_binding checkedOptimize_not_binding \
  mem_seqRegs_openFlat shippedRegsFromSource_of_hierGate regsFit_of_hstR_hst1 topshareM_regsFit_of_hstR_hst1 topshareQ_regsFit_of_hstR_hst1 \
  topshareM_hierGate topshareQ_hierGate deinline_cases; do
  grep -rn "^theorem $n\b" --include=*.lean Tools Sparkle Tests | head -2 | sed "s/^/LEMMA $n: /" | cut -c1-200
done
grep -n "^structure TypedIn" -A8 Tools/ShippingTextTyped.lean | sed 's/^/Tools\/ShippingTextTyped.lean:/' | head -10
