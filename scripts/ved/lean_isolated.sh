#!/usr/bin/env bash
# Per-case Lean runner for the U1 harness (MEASUREMENT ONLY): U1_LEAN="scripts/ved/lean_isolated.sh".
#
# Runs `lake env lean FILE` inside the build directory of THIS Pod's own successful
# `kjob lake build` of THIS tree (builds/<id>.json in $KJOB_STATE_DIR), so the case reads
# exactly the oleans that build checked (Lake verifies every trace). It replaces
# `kjob lake env lean`, which before manager PR #80 seeded from other trees without trace
# checks. Refuses (exit 97, a harness error) unless exactly one tree was built in this Pod,
# every build of it succeeded, and the tree is a clean checkout.
set -u
f=${1:?Lean file}
repo=$(git rev-parse --show-toplevel) || exit 97
state=${KJOB_STATE_DIR:?not inside a kjob Pod}
sel=$(python3 -I - "$state/builds" "$repo" <<'EOF'
import glob, json, os, sys
d, repo = sys.argv[1], os.path.realpath(sys.argv[2])
recs = []
for p in glob.glob(os.path.join(d, "*.json")):
    try:
        recs.append(json.load(open(p)))
    except (OSError, ValueError):
        pass
srcs = {os.path.realpath(r.get("source", "")) for r in recs}
if srcs != {repo}:
    sys.exit(f"lean_isolated: builds in this Pod are not all of {repo}: {sorted(srcs)}")
# a commit made after an earlier build in this Pod leaves that older build record behind: only the
# builds of the NEWEST tree state (the latest started build's source hash) count; the tree must
# still be clean (checked below), so that build is the one of this very tree
if recs:
    newest = max(recs, key=lambda r: r.get("started_at", 0)).get("source_sha256")
    recs = [r for r in recs if r.get("source_sha256") == newest]
ok = [r for r in recs if r.get("phase") == "succeeded" and r.get("exit_code") == 0]
if not ok or len(ok) != len(recs):
    sys.exit("lean_isolated: no build, or a build that did not succeed")
r = max(ok, key=lambda r: r.get("started_at", 0))
if not os.path.isdir(os.path.join(r["build_dir"], ".lake")):
    sys.exit("lean_isolated: build dir is gone: " + r["build_dir"])
print(r["build_dir"], r["toolchain"], r["build_id"], r["source_sha256"])
EOF
) || exit 97
read -r dir tc bid sha <<<"$sel"
[ -z "$(git -C "$repo" status --porcelain --untracked-files=all)" ] || { echo "lean_isolated: $repo is not clean" >&2; exit 97; }
echo "lean_isolated: build_id=$bid source_sha256=$sha head=$(git -C "$repo" rev-parse HEAD)" >&2
case "$f" in /*) ;; *) f="$PWD/$f" ;; esac
cd "$dir" && ELAN_HOME=${KJOB_BUILD_CACHE:-/build/cache}/elan exec elan run "$tc" lake env lean "$f"
