#!/usr/bin/env bash
# U0: run ONE generated case (one inventory row x one setting) in isolation.
#
# WRITTEN, NOT RUN (2026-11-08).  Design and the exact Job invocation:
# docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md (section 3).
#
# Usage (inside a kjob Pod, repo root, after `kjob lake build` of the imports):
#   scripts/ved/u0_case.sh OUT ROW SETTING            # one case
#   scripts/ved/u0_case.sh OUT --list ROWS.txt        # lines "ROW SETTING", serial, resumable
#   scripts/ved/u0_case.sh OUT --smoke-file FILE      # an existing deep test file as-is (historical comparison)
#   scripts/ved/u0_case.sh OUT --smoke-split FILE     # the same file, one variant per #verify_elab_deep
#
# OUT must be outside the source tree (e.g. "$(dirname "$KJOB_REPORT_PATH")/ved_u0").
# Per case: a fresh `lean` process (an earlier failure can not hide a later one),
# wall-clock limit U0_TMO seconds (default 1800), address-space limit U0_MEM_KB
# (default 12 GiB), peak RSS, rc, timeout flag.  Nothing is written into the tree.
set -u
OUT=${1:?OUT}; shift
REPO=$(git rev-parse --show-toplevel)
case "$(realpath -m "$OUT")/" in "$REPO"/*) echo "OUT must be outside the source tree" >&2; exit 2;; esac
mkdir -p "$OUT"
TMO=${U0_TMO:-1800}
MEMKB=${U0_MEM_KB:-12582912}
# each case is one fresh process of this command (word-split on purpose);
# `kjob lake env lean` sets LEAN_PATH from the node-local cached build
LEANCMD=${U0_LEAN:-kjob lake env lean}
SHA=$(git rev-parse HEAD)
DIRTY=$(git status --porcelain --untracked-files=no | wc -l)

# run CMD... with limits; write run.txt next to the outputs
limited_run() {
  local dir=$1; shift
  python3 -I - "$dir" "$TMO" "$MEMKB" "$@" <<'PY'
import os, resource, subprocess, sys, time
d, tmo, memkb, cmd = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4:]
env = dict(os.environ)
for ln in open(os.path.join(d, "case.env")) if os.path.exists(os.path.join(d, "case.env")) else []:
    k, _, v = ln.rstrip("\n").partition("=")
    if k: env[k] = v
env["SPARKLE_DEEP_TRACE"] = os.path.join(d, "stages.log")   # stage markers survive a kill
def lim():
    resource.setrlimit(resource.RLIMIT_AS, (memkb * 1024, memkb * 1024))
t0 = time.monotonic()
with open(os.path.join(d, "stdout.txt"), "w") as fo, open(os.path.join(d, "stderr.txt"), "w") as fe:
    p = subprocess.Popen(cmd, stdout=fo, stderr=fe, env=env, preexec_fn=lim)
    timed_out = "no"
    try:
        rc = p.wait(timeout=tmo)
    except subprocess.TimeoutExpired:
        p.kill(); rc = p.wait(); timed_out = "yes"
wall = time.monotonic() - t0
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
err = open(os.path.join(d, "stderr.txt"), errors="replace").read()
limit = "mem" if ("out of memory" in err or "std::bad_alloc" in err or rc in (-9, 137) and timed_out == "no") else ""
with open(os.path.join(d, "run.txt"), "w") as f:
    for k, v in [("rc", rc), ("timeout", timed_out), ("limit", limit), ("wall_s", f"{wall:.1f}"),
                 ("peak_rss_kb", ru.ru_maxrss), ("time_limit_s", tmo), ("mem_limit_kb", memkb),
                 ("sparkle_sha", os.environ.get("U0_SHA", "")), ("cmd", " ".join(cmd))]:
        f.write(f"{k}={v}\n")
PY
}

one_case() {
  local row=$1 setting=$2 dir
  dir=$(python3 -I scripts/ved/u0_gen.py --repo "$REPO" gen --row "$row" --setting "$setting" --out "$OUT/cases") || return 1
  if [ -f "$dir/run.txt" ] && [ -z "${REDO:-}" ]; then echo "skip $dir (done)"; return 0; fi
  U0_SHA="$SHA+dirty$DIRTY" limited_run "$dir" $LEANCMD "$dir/Case.lean"
  python3 -I scripts/ved/u0_gen.py --repo "$REPO" classify "$dir" >> "$OUT/results.tsv"
  echo "$row $setting $(grep -E '^(rc|timeout|wall_s)=' "$dir/run.txt" | tr '\n' ' ')"
}

[ -f "$OUT/results.tsv" ] || python3 -I scripts/ved/u0_gen.py header > "$OUT/results.tsv"
[ -f "$OUT/results_smoke.tsv" ] || python3 -I scripts/ved/u0_gen.py header > "$OUT/results_smoke.tsv"
{ echo "sparkle_sha=$SHA"; echo "dirty_files=$DIRTY"; echo "date=$(date -u +%FT%TZ)";
  echo "toolchain=$(cat lean-toolchain)"; echo "node=${KJOB_NODE:-$(hostname)}";
  echo "tmo=$TMO mem_kb=$MEMKB"; } > "$OUT/env.txt"

case "${1:-}" in
  --list)
    while read -r row setting; do
      [ -z "$row" ] && continue
      one_case "$row" "$setting"
    done < "${2:?ROWS.txt}" ;;
  --smoke-file)
    f=${2:?FILE}; d="$OUT/smoke/$(basename "$f" .lean)"; mkdir -p "$d"
    : > "$d/case.env"
    U0_SHA="$SHA+dirty$DIRTY" limited_run "$d" $LEANCMD "$(realpath "$f")"
    echo "smoke $f $(tr '\n' ' ' < "$d/run.txt")" ;;
  --smoke-split)
    f=${2:?FILE}
    for d in $(python3 -I scripts/ved/u0_gen.py --repo "$REPO" smoke-split "$f" --out "$OUT/smoke_split"); do
      if [ -f "$d/run.txt" ] && [ -z "${REDO:-}" ]; then echo "skip $d (done)"; continue; fi
      U0_SHA="$SHA+dirty$DIRTY" limited_run "$d" $LEANCMD "$d/Case.lean"
      python3 -I scripts/ved/u0_gen.py --repo "$REPO" classify "$d" >> "$OUT/results_smoke.tsv"
      echo "$d $(grep -E '^(rc|timeout|wall_s)=' "$d/run.txt" | tr '\n' ' ')"
    done ;;
  *)
    one_case "${1:?ROW}" "${2:?SETTING}" ;;
esac
