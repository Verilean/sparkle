#!/bin/bash
# Generates the machine part of GAP_INVENTORY.txt (run from the worktree root): gap Prop texts from the SRM22 source
# and file:line of every lemma the analysis cites.  usage: scripts/srm23/gen_inventory.sh > scripts/srm23/GAP_INVENTORY.gen.txt
echo "=== GAP PROP TEXT (Tools/ShippingSrm22Width.lean, verbatim) ==="
awk '/^def (InputsAreWires|ShippedRegsFromSource|SourceRegsKept|ShippedRegWidthLe|ShippedRegsAreSlots)/{p=1} p{print FILENAME":"FNR": "$0} /^$/{p=0}' Tools/ShippingSrm22Width.lean
echo "=== CITED LEMMAS (file:line of declaration) ==="
for n in wire_ne_clk weS_clk_rst clk_input weS_input declWidth_of_wire weOf_port refineCheck_regWidth refineCheck_regs regOf_some \
  mem_seqRegs_openFlat checkedOptimize_binding checkedOptimize_not_binding hierRefineCheck_inputs core_hierGate_anyAM \
  core_closed_typedIn_ranAM dropZW_inputs dropZW_wires_sub mergeChecked_ports weS_checkedOptimize_le checkedOptimize_ports_wires \
  declWidth_le_weS_input optimizeModule_ports optimizeModule_wires_subset deinline_cases hin_of_hinsFit hstX_of_hst3 regsFit_of_hstR_hst1 regsAtInit_of_hinit; do
  grep -rn "^theorem $n\b" --include=*.lean Tools Sparkle | head -2 | sed "s/^/LEMMA $n: /" | cut -c1-200
done
echo "=== DEFS ==="
grep -n "^def checkedOptimize\|^def hierRefineCheck\|^def hierBinds\|^def hierGate\|^def refineCheck\|^def regOf\|^def seqRegs\|^def openFlat\|^def openBody\|^def addClockResetIfSequential\|^def MachineWired\|^structure TypedIn" -r Sparkle Tools --include=*.lean | cut -c1-160
echo "=== INSTANCE b (from scripts/srm22/INVENTORY.txt) ==="
grep "S22INV|Tests.Compiler.SharedLeafMemKidIfaceTest.topshare[MQ]_svBoundsH_underComposedG|\(6\|7\|8\|9\|10\|12\)|" scripts/srm22/INVENTORY.txt | cut -c1-330
