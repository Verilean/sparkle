#!/usr/bin/env bash
# U0: thin wrapper over scripts/ved/u0_run.py (kept for the documented CLI).
#
# Usage (inside a kjob Pod, repo root, after `kjob lake build` of the imports):
#   scripts/ved/u0_case.sh OUT ROW SETTING [SV_GROUP]   # one case
#   scripts/ved/u0_case.sh OUT --list ROWS.txt          # lines "ROW SETTING [SV_GROUP]", resumable
#   scripts/ved/u0_case.sh OUT --smoke-file FILE        # an existing deep test file as-is
#   scripts/ved/u0_case.sh OUT --smoke-split FILE       # one variant per #verify_elab_deep
#
# Isolation, environment clearing, run identity/attempts, harness-error rows
# and the COMPLETE/INCOMPLETE summary are in u0_run.py (its docstring).  The
# exit status is u0_run.py's: 0 = COMPLETE, 3 = INCOMPLETE (harness errors or
# missing rows), other = the runner could not start.  Nothing is written into
# the source tree.  Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md.
set -u
OUT=${1:?OUT}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git rev-parse --show-toplevel)
case "${1:-}" in
  --list)        exec python3 -I "$HERE/u0_run.py" --repo "$REPO" --out "$OUT" list "${2:?ROWS.txt}" ;;
  --smoke-file)  exec python3 -I "$HERE/u0_run.py" --repo "$REPO" --out "$OUT" smoke-file "${2:?FILE}" ;;
  --smoke-split) exec python3 -I "$HERE/u0_run.py" --repo "$REPO" --out "$OUT" smoke-split "${2:?FILE}" ;;
  *)             exec python3 -I "$HERE/u0_run.py" --repo "$REPO" --out "$OUT" case "${1:?ROW}" "${2:?SETTING}" ${3:+"$3"} ;;
esac
