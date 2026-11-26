#!/usr/bin/env bash
# Measure what a new user of the research release waits for, using only the
# published instructions (README Quick Start, tutorial Ch07c, downstream smoke).
#
# Usage: scripts/research/ux_measure.sh LABEL SHA OUTDIR [REPO_URL]
#   LABEL   short name of the revision (baseline / candidate)
#   SHA     commit to clone (fixed, full or abbreviated)
#   OUTDIR  where ux-LABEL.tsv, logs and the environment dump are written
#   REPO_URL  clone URL (default https://github.com/Verilean/sparkle.git)
#
# Steps (each timed separately, one TSV row each):
#   a0 elan install            toolchain manager download
#   a1 toolchain install       `elan toolchain install $(cat lean-toolchain)`
#   a2 dependency fetch        `lake env true` (clones LSpec from the manifest)
#   a3 lake build (cold)       README Quick Start `lake build`
#   b1 lake build (warm)       unchanged rebuild
#   c1 lake build (leaf edit)  one-line edit of a leaf module of the default closure
#   c2 downstream cold / c3 downstream edit   MyBlinky project of downstream-smoke.yml
#   d0 lake build Tools.VedU1Entry   proof-tool libraries (Ch07c: "import Tools.VedU1Entry")
#   d1 synthesis only          `#synthesizeVerilog delay8` (Ch07c example)
#   d2 #ved_u1 delay8          synthesis + proof elaboration + kernel (profiler split)
#   e1 build IP.Crypto.Keccak256HW   the real IP's library
#   e2 #ved_u1 keccakRcHW      representative real-IP strict proof (profiler split)
#
# No cache is restored and nothing is read from outside the clone.  Peak RSS is
# GNU time's "Maximum resident set size": the largest single process of the
# step, not the sum over a process tree.
set -u
LABEL=${1:?label}; SHA=${2:?sha}; OUT=$(readlink -f "${3:?outdir}")
REPO_URL=${4:-https://github.com/Verilean/sparkle.git}
mkdir -p "$OUT"
TSV="$OUT/ux-$LABEL.tsv"
WORK=${UX_WORK:-$OUT/work-$LABEL}
printf 'label\tstep\tdescription\twall_s\tuser_s\tsys_s\tpeak_rss_mb\trc\tnote\n' > "$TSV"

TIMEBIN=$(command -v /usr/bin/time || command -v time)
now() { date +%s.%N; }

# run STEP DESC CMD...   (stdout+stderr go to $OUT/$LABEL-STEP.log)
run() {
  local step=$1 desc=$2; shift 2
  local log="$OUT/$LABEL-$step.log" tf="$OUT/$LABEL-$step.time"
  local t0 t1 rc
  echo "=== [$LABEL] $step: $desc"
  t0=$(now)
  "$TIMEBIN" -v -o "$tf" bash -c '"$@" 2>&1 | while IFS= read -r l; do printf "%s %s\n" "$(date +%s.%N)" "$l"; done; exit ${PIPESTATUS[0]}' _ "$@" > "$log"
  rc=$?
  t1=$(now)
  local wall user sys rss
  wall=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.1f", b-a}')
  user=$(awk -F': ' '/User time/{print $2}' "$tf")
  sys=$(awk -F': ' '/System time/{print $2}' "$tf")
  rss=$(awk -F': ' '/Maximum resident/{printf "%.0f", $2/1024}' "$tf")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$LABEL" "$step" "$desc" "$wall" "$user" "$sys" "$rss" "$rc" "${NOTE:-}" >> "$TSV"
  echo "    wall=${wall}s user=${user}s sys=${sys}s rss=${rss}MB rc=$rc"
  NOTE=
  return 0
}

# Lean's profiler prints "cumulative profiling times:" followed by one
# "<category> <time>" line per category (type checking = kernel, elaboration,
# tactic execution, simp, ...).  Append them, and whether the proof was
# accepted, to the note column of the step's TSV row.
annotate() {
  local log=$1 verdict=NOT-accepted prof
  grep -q 'VED U1 OK' "$log" && verdict=accepted
  prof=$(sed -E 's/^[0-9.]+ //' "$log" | awk '/cumulative profiling times/{f=1;next} f&&/^[ \t]+[a-zA-Z]/{l=$0;gsub(/^[ \t]+/,"",l);printf "%s; ",l;next} f{f=0}')
  awk -F'\t' -v OFS='\t' -v n="$verdict; $prof" 'NR>1{last=NR} {l[NR]=$0} END{for(i=1;i<=NR;i++){ if(i==last){split(l[i],c,"\t"); c[9]=c[9] " [" n "]"; l[i]=c[1];for(j=2;j<=9;j++)l[i]=l[i] OFS c[j]} print l[i]}}' "$TSV" > "$TSV.tmp" && mv "$TSV.tmp" "$TSV"
}

# ---- environment and cache state ------------------------------------------
{
  echo "label=$LABEL sha=$SHA"
  echo "date=$(date -u +%FT%TZ)"
  echo "nproc=$(nproc)"
  free -g
  df -h / "$OUT" | head -5
  uname -a
  echo "runner: ${RUNNER_NAME:-local} image=${ImageVersion:-unknown}"
  echo "elan before: $(command -v elan || echo none); ~/.elan: $(ls -d "$HOME/.elan" 2>/dev/null || echo absent)"
  echo "lean on PATH before: $(command -v lean || echo none)"
  echo "cache state: no cache restore; fresh clone at $SHA; no .lake; LAKE_CACHE_DIR=${LAKE_CACHE_DIR:-unset}"
} | tee "$OUT/env-$LABEL.txt"

# ---- a0/a1: toolchain download ---------------------------------------------
rm -rf "$WORK"
run a_clone "git clone + checkout $SHA" bash -c "git clone --quiet '$REPO_URL' '$WORK' && git -C '$WORK' checkout --quiet '$SHA'"
cd "$WORK" || exit 1
git rev-parse HEAD | tee "$OUT/head-$LABEL.txt"
TC=$(cat lean-toolchain)
if [ -z "${UX_SKIP_ELAN:-}" ]; then
run a0 "elan install (no toolchain)" bash -c 'curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none'
export PATH="$HOME/.elan/bin:$PATH"

run a1 "elan toolchain install $TC" elan toolchain install "$TC"
elan default "$TC" >/dev/null 2>&1
else echo "UX_SKIP_ELAN set: toolchain steps skipped (debug runs only)"; fi

# ---- a2/a3: dependency fetch and the normal build -------------------------
run a2 "dependency fetch (lake env true: clones LSpec)" lake env true
NOTE="README Quick Start: lake build (default targets)"
run a3 "lake build (cold, default target)" lake build

# ---- b: unchanged rebuild --------------------------------------------------
run b1 "lake build (unchanged, warm)" lake build

# ---- c1: small edit of a leaf module in the default closure -----------------
LEAF=Sparkle/Utils/HexLoader.lean
echo "" >> "$LEAF"; echo "def uxProbe : Nat := 1" >> "$LEAF"
NOTE="edit: append one def to $LEAF"
run c1 "lake build after a one-line edit of a leaf module" lake build
git checkout --quiet -- "$LEAF"

# ---- c2/c3: downstream project (downstream-smoke.yml) ----------------------
DS="$OUT/my-blinky-$LABEL"; rm -rf "$DS"; mkdir -p "$DS/MyBlinky"
cp lean-toolchain "$DS/lean-toolchain"
cat > "$DS/lakefile.toml" <<EOF
name = "my-blinky"
defaultTargets = ["MyBlinky"]

[[require]]
name = "sparkle"
git = "$REPO_URL"
rev = "$(git rev-parse HEAD)"

[[lean_lib]]
name = "MyBlinky"
EOF
cat > "$DS/MyBlinky/Counter.lean" <<'EOF'
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace MyBlinky.Counter

/-- A 4-bit counter that increments every cycle. -/
def blinky {dom : DomainConfig} : Signal dom (BitVec 4) :=
  circuit do
    let count ← Signal.reg 0#4
    count <~ count + 1#4
    return count

end MyBlinky.Counter
EOF
echo "import MyBlinky.Counter" > "$DS/MyBlinky.lean"
( cd "$DS" || exit 1
  # the clone's step-a elan default does not apply here; the toolchain is already installed
  run c2a "downstream: lake update (resolve sparkle by git rev)" lake update
  NOTE="Sparkle is built again inside the downstream project's own .lake"
  run c2 "downstream: lake build (cold, Sparkle + MyBlinky)" lake build
  sed -i 's/count + 1#4/count + 2#4/' MyBlinky/Counter.lean
  NOTE="edit: increment 1 -> 2 in the user's circuit"
  run c3 "downstream: lake build after a one-line circuit edit" lake build
)

# ---- d: short tutorial example (Ch07c, #ved_u1 delay8) ----------------------
NOTE="Ch07c: 'You use them with import Tools.VedU1Entry inside the repository'"
run d0 "lake build Tools.VedU1Entry (proof-tool libraries)" lake build Tools.VedU1Entry

cat > "$OUT/ux_synth.lean" <<'EOF'
import Sparkle
open Sparkle.Core.Domain Sparkle.Core.Signal

def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

#synthesizeVerilog delay8
EOF
cat > "$OUT/ux_ved.lean" <<'EOF'
import Tools.VedU1Entry
open Sparkle.Core.Domain Sparkle.Core.Signal

def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

set_option profiler true
set_option profiler.threshold 100000
#ved_u1 delay8
EOF
run d1 "Ch07c example: #synthesizeVerilog delay8 only" lake env lean "$OUT/ux_synth.lean"
run d2 "Ch07c example: #ved_u1 delay8 (synthesis + proof + kernel)" lake env lean "$OUT/ux_ved.lean"
annotate "$OUT/$LABEL-d2.log"

# ---- e: representative real IP (keccakRcHW: 32 x 64-bit constants, 5-bit index)
NOTE="IP library of the real-IP proof"
run e1 "lake build IP.Crypto.Keccak256HW" lake build IP.Crypto.Keccak256HW
cat > "$OUT/ux_ip.lean" <<'EOF'
import Tools.VedU1Entry
import IP.Crypto.Keccak256HW

set_option profiler true
set_option profiler.threshold 100000
#ved_u1 Sparkle.IP.Crypto.Keccak256HW.keccakRcHW
EOF
run e2 "real IP: #ved_u1 keccakRcHW (synthesis + proof + kernel)" lake env lean "$OUT/ux_ip.lean"
annotate "$OUT/$LABEL-e2.log"

# CI check files for the same procedures (present only where the revision has them)
for t in Tests.Ved.U1EntryCheck Tests.Ved.U1KeccakRcCheck; do
  f=$(echo "$t" | tr . /).lean
  if [ -f "$f" ]; then
    NOTE="CI step target, for comparison with the user procedure"
    run "x_${t##*.}" "lake build $t" lake build "$t"
  else
    printf '%s\tx_%s\tlake build %s\t\t\t\t\t\tabsent at this revision\n' "$LABEL" "${t##*.}" "$t" >> "$TSV"
  fi
done

echo; column -t -s$'\t' "$TSV" | cut -c1-200
