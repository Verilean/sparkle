#!/bin/bash
# Machine part of K1_INVENTORY.txt (run from worktree root): verbatim statements + file:line of the producer/consumer chain for `regs`.
show() { # file startpattern [nlines=60]  (prints N lines from the def/theorem header, with file:line)
  awk -v pat="$2" -v F="$1" -v N="${3:-60}" '$0 ~ pat {p=1} p {print F":"FNR": "$0; if (++c>=N) exit}' "$1"; }
echo "=== MachineWired (verbatim) ==="; show Tools/ShippingMachineEntry.lean '^def MachineWired' 101
echo "=== MachinePreservesX (verbatim) ==="; show Tools/ShippingMachineEntry.lean '^def MachinePreservesX' 34
echo "=== synthesizeMachineCertified_soundX (verbatim) ==="; show Tools/ShippingMachineEntry.lean '^theorem synthesizeMachineCertified_soundX' 32
echo "=== machine_traceX (verbatim) ==="; show Tools/ShippingMachineTraceX.lean '^theorem machine_traceX' 32
echo "=== MachineTraceLBX (verbatim) ==="; show Tools/ShippingMachineTraceX.lean '^def MachineTraceLBX' 42
echo "=== ComposedGW (verbatim) ==="; show Tools/ShippingComposedGW.lean '^def ComposedGW ' 36
echo "=== composedGW_of_T (verbatim) ==="; show Tools/ShippingComposedGW.lean '^theorem composedGW_of_T' 60
echo "=== machine_linkedT_callsRGW conclusion (verbatim) ==="
awk '/^theorem machine_linkedT_callsRGW/{f=1} f && /∃ ids : List FVarId/{p=1} p{print FILENAME":"FNR": "$0} p && /:= by$/{exit}' Tools/ShippingComposedGW.lean | head -40
echo "=== producer sites for regs / ps / ids / cache ==="
grep -n "obtain ⟨ids, cache, returned\|let ps := inputPorts\|have wired : MachineWired\|refine ⟨ps.map Port.name\|refine ⟨ids, nd, len, cache" Tools/ShippingMachineEntry.lean | sed 's/^/Tools\/ShippingMachineEntry.lean:/'
echo "=== machPorts def ==="; show Tools/ShippingMachineEntry.lean '^def machPorts'
echo "=== MachineWired's slot->register conjunct (last conjunct), verbatim ==="
awk '/^def MachineWired/{f=1} f && /with or without calls, each slot/{p=1} p{print FILENAME":"FNR": "$0} p && /body\)$/{exit}' Tools/ShippingMachineEntry.lean
echo "=== every consumer of MachineWired/regs between soundX and ComposedGW (file:line of 'regs' in binder/obtain) ==="
grep -n "regs" Tools/ShippingMachineTraceX.lean | grep -n "∃\|obtain" | head -20
echo "=== uses of 'regs' pinning beyond Nodup/length (any hypothesis mentioning machPorts/ps with regs) ==="
grep -rn "regs = \|regs ==\|(ps.map Port.name) =\|regs.Perm\|regs ~" --include=*.lean Tools | grep -v "^Tools/ShippingSrm2[0-9]" | head -20
echo "=== SourceInputs / Admissible: which binders it covers in ComposedGW (take kD of bsIn only) ==="
grep -n "SourceInputs declName (d.bsIn.take kD)" Tools/ShippingComposedGW.lean | head -3
grep -n "^def SourceInputs" -A4 Tools/ShippingMixedSourceBridge.lean | sed 's/^/Tools\/ShippingMixedSourceBridge.lean:/' | head -6
echo "=== Mathlib-free? ==="; grep -c "import Mathlib" Tools/ShippingMachineEntry.lean
