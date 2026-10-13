#!/usr/bin/env bash
# Writer simulation of the eight gate-route parents (parentUse, wrapAdd,
# parentMix, parentTwoCalls, parentRepeat, parentCmp, parentNested,
# wrapPick): the text of the REAL command of the tree (#writeVerilogDesign)
# against the SOURCE (the Lean declaration evaluated cycle by cycle) on one
# stimulus. An integration criterion of the environment-capture unit
# (docs/parallel/M-env-capture-a.md): run it on poc and on the candidate; the
# eight lines must read `command==source T` on both.
#
# WRITTEN, NOT RUN. The machinery is the tree's own module_name_sim (stimulus,
# test bench, comparison), derived at run time by gate_parents_sim.py; only
# the declarations differ.
#
#   scripts/shipping-coverage/cgrun.sh -n gateparentsim -m 3G -t 900 -- \
#     scripts/shipping-coverage/gate_parents_sim.sh
#
# One line per declaration:
#   GATEPARENTSIM <decl>: command==source <T/F/-> x-cycles=<n> cycles=<n>
#
# Evidence on one stimulus, not a proof. Exits 0 always (it reports).
# Requires a completed `lake build Tests.Compiler.SlotlessParentProbeTest
# Tests.Compiler.CallWidthHuntTest`; must NOT run next to a `lake build`.
# Files: .lake/build/gen/gate-parents-sim/ (and -src/ for the derived driver).
set -u
cd "$(dirname "$0")/../.."
GEN=.lake/build/gen/gate-parents-sim-src
mkdir -p "$GEN"
if ! python3 scripts/shipping-coverage/gate_parents_sim.py "$GEN"; then
  echo "GATEPARENTSIM: NOT RUN — the derivation from module_name_sim failed (the template moved)"
  exit 0
fi
exec bash "$GEN/gate_parents_sim_run.sh"
