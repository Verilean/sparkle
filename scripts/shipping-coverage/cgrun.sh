#!/usr/bin/env bash
# cgrun.sh — run ONE heavy command (lake / lean) inside its own cgroup, with
# memory limits, a timeout and a saved record of what happened.
#
#   cgrun.sh [-n name] [-m MemoryMax] [-g MemoryHigh] [-s MemorySwapMax]
#            [-t timeoutSec] [-j leanThreads] [-d workdir] -- command …
#
# The command runs as a transient systemd --user SERVICE (so it and every
# descendant are in the unit's cgroup; this shell, Claude and SSH are not).
# Only one such unit at a time (a lock). Limits are READ BACK from the
# cgroup of the unit's real main PID before the run counts as protected.
# The record (settings read back, PIDs, samples of memory.current, peak,
# memory.events, unit result, exit code, log) is kept under
# ~/sparkle-work/runs/<stamp>-<name>/. The watcher ends when the unit ends
# or the deadline passes — it does not wait for a marker.
set -u
NAME=job; MAX=3G; HIGH=""; SWAP=0; TMO=600; THREADS=2; DIR=$PWD
while getopts "n:m:g:s:t:j:d:" o; do case $o in
  n) NAME=$OPTARG;; m) MAX=$OPTARG;; g) HIGH=$OPTARG;; s) SWAP=$OPTARG;;
  t) TMO=$OPTARG;; j) THREADS=$OPTARG;; d) DIR=$OPTARG;; *) exit 2;; esac; done
shift $((OPTIND-1)); [ "${1:-}" = "--" ] && shift
[ $# -ge 1 ] || { echo "usage: cgrun.sh [opts] -- command …" >&2; exit 2; }

ROOT=$HOME/sparkle-work/runs; mkdir -p "$ROOT"
exec 9>"$ROOT/.lock"
flock -n 9 || { echo "cgrun: another protected job is running: $(cat "$ROOT/.current" 2>/dev/null)" >&2; exit 75; }

to_bytes() { numfmt --from=iec "$1"; }
MAXB=$(to_bytes "$MAX")
[ -n "$HIGH" ] || HIGH=$(( MAXB * 85 / 100 ))
HIGHB=$(to_bytes "$HIGH")
# never above what the host can give while leaving 1.5 GiB for everything else
AVAIL=$(( $(awk '/MemAvailable/{print $2}' /proc/meminfo) * 1024 ))
ROOM=$(( AVAIL - 1536*1024*1024 ))
if [ "$MAXB" -gt "$ROOM" ]; then
  echo "cgrun: MemoryMax $MAXB exceeds available-1.5GiB ($ROOM); refusing" >&2; exit 76
fi

STAMP=$(date +%Y%m%d-%H%M%S); UNIT="sparkle-$NAME-$STAMP"
OUT="$ROOT/$STAMP-$NAME"; mkdir -p "$OUT"
echo "$UNIT $OUT" > "$ROOT/.current"
export -p | grep -v ' \(BASHOPTS\|BASH_VERSINFO\|EUID\|PPID\|SHELLOPTS\|UID\)=' > "$OUT/env.sh"
printf '%q ' "$@" > "$OUT/command.txt"
cat > "$OUT/inner.sh" <<EOF
#!/usr/bin/env bash
source "$OUT/env.sh" 2>/dev/null
export LEAN_NUM_THREADS=$THREADS
cd "$DIR" || exit 97
$(printf '%q ' "$@")
rc=\$?
echo \$rc > "$OUT/exitcode"
exit \$rc
EOF
chmod +x "$OUT/inner.sh"

systemd-run --user --quiet --unit="$UNIT" --service-type=exec \
  -p MemoryAccounting=yes -p MemoryMax="$MAXB" -p MemoryHigh="$HIGHB" \
  -p MemorySwapMax="$SWAP" -p OOMPolicy=kill -p RuntimeMaxSec="$TMO" \
  -p KillMode=control-group -p TimeoutStopSec=10 \
  -p StandardOutput="append:$OUT/log.txt" -p StandardError="append:$OUT/log.txt" \
  "$(command -v bash)" "$OUT/inner.sh" || { echo "cgrun: systemd-run failed" >&2; exit 77; }

# read the limits back from the cgroup of the real PID
PID=$(systemctl --user show -p MainPID --value "$UNIT")
CG=""; [ "$PID" != 0 ] && [ -r /proc/$PID/cgroup ] && CG=/sys/fs/cgroup$(cut -d: -f3 /proc/$PID/cgroup)
{
  echo "unit=$UNIT"; echo "mainpid=$PID"; echo "cgroup=$CG"
  echo "self_cgroup=$(cut -d: -f3 /proc/$$/cgroup)"
  for f in memory.max memory.high memory.swap.max memory.oom.group; do
    echo "$f=$(cat "$CG/$f" 2>/dev/null)"; done
  echo "requested: max=$MAXB high=$HIGHB swap=$SWAP timeout=$TMO threads=$THREADS"
} > "$OUT/protect.txt"
RB=$(cat "$CG/memory.max" 2>/dev/null)
if [ -n "$CG" ] && [ "$RB" != "$MAXB" ]; then
  echo "cgrun: limit not in force (memory.max read back '$RB'); stopping the unit" >&2
  systemctl --user stop "$UNIT"; echo "result=unprotected" > "$OUT/result.txt"; exit 78
fi
case "$CG" in *"$UNIT"*) ;; "") ;; *)
  echo "cgrun: main PID is not in the unit's cgroup ($CG); stopping" >&2
  systemctl --user stop "$UNIT"; exit 78;; esac

# watch: by unit state and a deadline
DEADLINE=$(( $(date +%s) + TMO + 30 )); PEAKSEEN=0; MAXPROCS=0
while :; do
  ST=$(systemctl --user show -p ActiveState --value "$UNIT")
  [ "$ST" = active ] || [ "$ST" = activating ] || [ "$ST" = deactivating ] || break
  if [ -n "$CG" ] && [ -r "$CG/memory.current" ]; then
    CUR=$(cat "$CG/memory.current" 2>/dev/null || echo 0)
    [ "$CUR" -gt "$PEAKSEEN" ] && PEAKSEEN=$CUR
    PROCS=$(wc -l < "$CG/cgroup.procs" 2>/dev/null || echo 0)
    NLEAN=$(for p in $(cat "$CG/cgroup.procs" 2>/dev/null); do cat /proc/$p/comm 2>/dev/null; done | grep -c '^lean$')
    [ "$NLEAN" -gt "$MAXPROCS" ] && MAXPROCS=$NLEAN
    echo "$(date +%s) current=$CUR procs=$PROCS lean=$NLEAN" >> "$OUT/samples.txt"
    cat "$CG/memory.events" > "$OUT/events.last" 2>/dev/null
    cat "$CG/memory.peak" > "$OUT/peak.last" 2>/dev/null
    cat "$CG/cgroup.procs" > "$OUT/procs.last" 2>/dev/null
  fi
  if [ "$(date +%s)" -gt "$DEADLINE" ]; then
    echo "cgrun: deadline passed; stopping the unit" >&2; systemctl --user stop "$UNIT"; break
  fi
  sleep 1
done

RES=$(systemctl --user show -p Result --value "$UNIT")
CODE=$(cat "$OUT/exitcode" 2>/dev/null || echo none)
# a unit that ended without the command's exit code was killed (limit, timeout)
[ "$CODE" = none ] && [ "$RES" = success ] && RES=killed-no-exit-code
[ "$CODE" != 0 ] && [ "$RES" = success ] && RES=exit-code
SPEAK=$(systemctl --user show -p MemoryPeak --value "$UNIT")
{
  echo "result=$RES"; echo "exit=$CODE"
  echo "memory_peak_systemd=$SPEAK"; echo "memory_peak_file=$(cat "$OUT/peak.last" 2>/dev/null)"
  echo "memory_current_max_sampled=$PEAKSEEN"; echo "max_concurrent_lean=$MAXPROCS"
  echo "events: $(tr '\n' ' ' < "$OUT/events.last" 2>/dev/null)"
} > "$OUT/result.txt"
systemctl --user reset-failed "$UNIT" 2>/dev/null
rm -f "$ROOT/.current"
echo "== $OUT"; cat "$OUT/protect.txt" "$OUT/result.txt"
[ "$RES" = success ] && exit 0
[ "$RES" = oom-kill ] && exit 137
[ "$RES" = timeout ] && exit 124
[ "$CODE" = none ] && exit 1
exit "$CODE"
