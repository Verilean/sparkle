#!/bin/sh
# machine part of K0N_INVENTORY.txt: verbatim file:line excerpts (run from the worktree root)
show() { f=$1; a=$2; b=$3; echo "=== $f:$a-$b ==="; sed -n "${a},${b}p" "$f" | awk -v s="$a" -v f="$f" '{printf "%s:%d: %s\n", f, s+NR-1, $0}'; }
show Tools/ShippingParentRanA.lean 47 60
show Tools/ShippingMachineEntry.lean 948 956
show Tools/ShippingMachineInst.lean 144 151
show Tools/ShippingCloseMachineFacts.lean 169 182
show Tools/ShippingClosedTransitionTyped.lean 63 82
show Tools/ShippingMixedEntrySoundness.lean 434 443
show Tools/ShippingMachineEntry.lean 654 662
show Tools/ShippingMachineEntry.lean 686 696
show Tools/ShippingMachineEntry.lean 750 754
show Tools/ShippingMachineEntry.lean 1035 1052
show Tools/ShippingMachineEntry.lean 1113 1113
show Tools/ShippingMachineEntry.lean 1439 1440
show Tools/ShippingMachineEntry.lean 2037 2038
show Tools/ShippingMachineDepthRun.lean 34 47
show Tools/ShippingComposedGW.lean 181 205
show Tools/ShippingSrm26Order.lean 92 100
show Tools/ShippingSrm25Init.lean 67 70
show Tools/ShippingSrm17Ran.lean 52 52
show Tools/ShippingSrm17Ran.lean 87 96
