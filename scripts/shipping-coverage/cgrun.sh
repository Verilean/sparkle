#!/usr/bin/env bash
# cgrun.sh — run ONE heavy command (lake / lean) inside its own cgroup, with
# memory limits, a timeout and a saved record of what happened.
#
#   cgrun.sh [-n name] [-m MemoryMax] [-g MemoryHigh] [-s MemorySwapMax]
#            [-t timeoutSec] [-j leanThreads] [-d workdir] -- command …
#   cgrun.sh -S            # list the protected jobs alive now
#
# The command runs as a transient systemd --user SERVICE (so it and every
# descendant are in the unit's cgroup; this shell, Claude and SSH are not).
#
# * GATE. The unit starts with a holder that waits; the payload is started
#   only after this script has read, from the unit's ControlGroup and from the
#   cgroup of its real main PID, that the PID is in the unit's cgroup and that
#   memory.max / memory.high / memory.swap.max / memory.oom.group are the
#   requested values. Anything unread or different: the unit is stopped, the
#   payload never runs, exit 78. An unverified run is never a success.
# * ONE JOB. Refused (exit 75) while any `sparkle-*` service of this user is
#   alive — asked of systemd, not of a lock file, so a job whose watcher was
#   lost (SSH drop, SIGKILL) still blocks a second one. The flock only
#   serialises two watchers starting at once.
# * A signal to the watcher stops the unit and waits for it. A watcher that is
#   killed outright leaves the unit to its own RuntimeMaxSec and MemoryMax.
# * The record (settings read back, PIDs, samples, peak, memory.events, unit
#   result, exit code, log) is kept, private to the user, under
#   ~/sparkle-work/runs/<stamp>-<name>/. Only an allow-list of environment
#   variables is passed and stored.
set -u
ROOT=$HOME/sparkle-work/runs
alive() { systemctl --user list-units --type=service --state=active,activating,deactivating,reloading \
            --no-legend --plain 'sparkle-*' 2>/dev/null | awk '{print $1}'; }
if [ "${1:-}" = "-S" ]; then alive; exit 0; fi

NAME=job; MAX=3G; HIGH=""; SWAP=0; TMO=600; THREADS=2; DIR=$PWD
while getopts "n:m:g:s:t:j:d:" o; do case $o in
  n) NAME=$OPTARG;; m) MAX=$OPTARG;; g) HIGH=$OPTARG;; s) SWAP=$OPTARG;;
  t) TMO=$OPTARG;; j) THREADS=$OPTARG;; d) DIR=$OPTARG;; *) exit 2;; esac; done
shift $((OPTIND-1)); [ "${1:-}" = "--" ] && shift
[ $# -ge 1 ] || { echo "usage: cgrun.sh [opts] -- command …" >&2; exit 2; }

umask 077
mkdir -p "$ROOT"; chmod 700 "$ROOT"
exec 9>"$ROOT/.lock"
flock -n 9 || { echo "cgrun: another cgrun is starting or watching a job" >&2; exit 75; }
LIVE=$(alive)
if [ -n "$LIVE" ]; then
  echo "cgrun: a protected job is still alive (its watcher may be gone): $LIVE" >&2
  echo "       record: $(cat "$ROOT/.current" 2>/dev/null)" >&2
  exit 75
fi

PAGE=$(getconf PAGESIZE)
to_bytes() { numfmt --from=iec "$1"; }
floor_page() { echo $(( $1 / PAGE * PAGE )); }
MAXB=$(floor_page "$(to_bytes "$MAX")")
[ -n "$HIGH" ] || HIGH=$(( MAXB * 85 / 100 ))
HIGHB=$(floor_page "$(to_bytes "$HIGH")")
SWAPB=$(floor_page "$(to_bytes "$SWAP")")
[ "$HIGHB" -lt "$MAXB" ] || { echo "cgrun: MemoryHigh must be below MemoryMax" >&2; exit 2; }
# never above what the host can give while leaving 1.5 GiB for everything else
AVAIL=$(( $(awk '/MemAvailable/{print $2}' /proc/meminfo) * 1024 ))
ROOM=$(( AVAIL - 1536*1024*1024 ))
if [ "$MAXB" -gt "$ROOM" ]; then
  echo "cgrun: MemoryMax $MAXB exceeds available-1.5GiB ($ROOM); refusing" >&2; exit 76
fi

STAMP=$(date +%Y%m%d-%H%M%S); UNIT="sparkle-$NAME-$STAMP"
OUT="$ROOT/$STAMP-$NAME"; mkdir -p "$OUT"
echo "$UNIT $OUT" > "$ROOT/.current"

# the environment the payload gets: an allow-list (no tokens, no agent sockets)
KEEP='^(PATH|HOME|USER|LOGNAME|SHELL|LANG|LC_[A-Z_]*|TZ|TMPDIR|TERM|ELAN_[A-Z_]*|LEAN_[A-Z_]*|LAKE[A-Z_]*|NIX_[A-Za-z0-9_]*|CC|CXX|AR|LD|PKG_CONFIG[A-Z_]*|LD_LIBRARY_PATH|LIBRARY_PATH|C_INCLUDE_PATH|CPATH|XDG_RUNTIME_DIR|VC_[A-Z_]*|SPARKLE_[A-Z_]*|ENDPOINT_JOBS|SIMX_JOBS)$'
: > "$OUT/env.sh"
while IFS='=' read -r -d '' k v; do
  [[ $k =~ $KEEP ]] && printf 'export %s=%q\n' "$k" "$v" >> "$OUT/env.sh"
done < <(env -0)
printf '%q ' "$@" > "$OUT/command.txt"
cat > "$OUT/inner.sh" <<EOF
#!/usr/bin/env bash
# holder: the payload starts only when the watcher has verified the cgroup
i=0
while [ ! -e "$OUT/go" ]; do
  i=\$((i+1)); [ \$i -gt 300 ] && { echo 98 > "$OUT/exitcode"; exit 98; }
  sleep 0.1
done
source "$OUT/env.sh"
export LEAN_NUM_THREADS=$THREADS
cd "$DIR" || { echo 97 > "$OUT/exitcode"; exit 97; }
$(printf '%q ' "$@")
rc=\$?
echo \$rc > "$OUT/exitcode"
exit \$rc
EOF
chmod 700 "$OUT/inner.sh"

stop_unit() {
  systemctl --user stop "$UNIT" 2>/dev/null
  for _ in $(seq 1 150); do
    [ -z "$(alive | grep -Fx "$UNIT.service")" ] && break; sleep 0.1
  done
}
trap 'echo "cgrun: signal — stopping $UNIT" >&2; stop_unit; echo "result=watcher-signalled" > "$OUT/result.txt"; rm -f "$ROOT/.current"; exit 130' INT TERM HUP

systemd-run --user --quiet --unit="$UNIT" --service-type=exec \
  --setenv=PATH="$PATH" \
  -p MemoryAccounting=yes -p MemoryMax="$MAXB" -p MemoryHigh="$HIGHB" \
  -p MemorySwapMax="$SWAPB" -p OOMPolicy=kill -p RuntimeMaxSec="$TMO" \
  -p KillMode=control-group -p TimeoutStopSec=10 \
  -p StandardOutput="append:$OUT/log.txt" -p StandardError="append:$OUT/log.txt" \
  "$(command -v bash)" "$OUT/inner.sh" || { echo "cgrun: systemd-run failed" >&2; rm -f "$ROOT/.current"; exit 77; }

# ---- the gate: nothing below may be skipped or left unread -------------------
fail_gate() {
  echo "cgrun: NOT PROTECTED — $1; the payload was not started" >&2
  { echo "result=unprotected"; echo "reason=$1"; } > "$OUT/result.txt"
  stop_unit; rm -f "$ROOT/.current"; exit 78
}
PID=$(systemctl --user show -p MainPID --value "$UNIT" 2>/dev/null)
UCG=$(systemctl --user show -p ControlGroup --value "$UNIT" 2>/dev/null)
[ -n "$PID" ] && [ "$PID" != 0 ] || fail_gate "no main PID"
[ -n "$UCG" ] || fail_gate "the unit has no ControlGroup"
case "$UCG" in *"/$UNIT.service") ;; *) fail_gate "ControlGroup '$UCG' is not the unit's";; esac
PCG=$(cut -d: -f3 "/proc/$PID/cgroup" 2>/dev/null) || true
[ "$PCG" = "$UCG" ] || fail_gate "PID $PID is in '$PCG', not in '$UCG'"
SELF=$(cut -d: -f3 /proc/$$/cgroup)
[ "$SELF" != "$UCG" ] || fail_gate "the watcher is inside the limited cgroup"
CG=/sys/fs/cgroup$UCG
rd() { cat "$CG/$1" 2>/dev/null || echo UNREAD; }
RMAX=$(rd memory.max); RHIGH=$(rd memory.high); RSWAP=$(rd memory.swap.max); RGRP=$(rd memory.oom.group)
{
  echo "unit=$UNIT"; echo "mainpid=$PID"; echo "cgroup=$CG"; echo "self_cgroup=$SELF"
  echo "memory.max=$RMAX"; echo "memory.high=$RHIGH"; echo "memory.swap.max=$RSWAP"; echo "memory.oom.group=$RGRP"
  echo "requested: max=$MAXB high=$HIGHB swap=$SWAPB group=1 timeout=$TMO threads=$THREADS"
} > "$OUT/protect.txt"
# (self-test of the gate only: pretend another limit was asked)
[ -n "${CGRUN_SELFTEST_MISMATCH:-}" ] && MAXB=$(( MAXB + PAGE ))
[ "$RMAX" = "$MAXB" ]   || fail_gate "memory.max is '$RMAX', asked $MAXB"
[ "$RHIGH" = "$HIGHB" ] || fail_gate "memory.high is '$RHIGH', asked $HIGHB"
[ "$RSWAP" = "$SWAPB" ] || fail_gate "memory.swap.max is '$RSWAP', asked $SWAPB"
[ "$RGRP" = 1 ]         || fail_gate "memory.oom.group is '$RGRP', asked 1"
echo "verified=yes" >> "$OUT/protect.txt"
: > "$OUT/go"

# ---- watch: by unit state and a deadline ------------------------------------
DEADLINE=$(( $(date +%s) + TMO + 30 )); PEAKSEEN=0; MAXPROCS=0
: > "$OUT/events.last"
while :; do
  ST=$(systemctl --user show -p ActiveState --value "$UNIT")
  [ "$ST" = active ] || [ "$ST" = activating ] || [ "$ST" = deactivating ] || break
  if [ -r "$CG/memory.current" ]; then
    CUR=$(cat "$CG/memory.current" 2>/dev/null || echo 0)
    [ "${CUR:-0}" -gt "$PEAKSEEN" ] && PEAKSEEN=$CUR
    PROCS=$(wc -l < "$CG/cgroup.procs" 2>/dev/null || echo 0)
    NLEAN=$(for p in $(cat "$CG/cgroup.procs" 2>/dev/null); do cat /proc/$p/comm 2>/dev/null; done | grep -c '^lean$')
    [ "$NLEAN" -gt "$MAXPROCS" ] && MAXPROCS=$NLEAN
    echo "$(date +%s) current=$CUR procs=$PROCS lean=$NLEAN" >> "$OUT/samples.txt"
    cat "$CG/memory.events" > "$OUT/events.tmp" 2>/dev/null && mv "$OUT/events.tmp" "$OUT/events.last"
    cat "$CG/memory.peak" > "$OUT/peak.tmp" 2>/dev/null && mv "$OUT/peak.tmp" "$OUT/peak.last"
  fi
  if [ "$(date +%s)" -gt "$DEADLINE" ]; then
    echo "cgrun: deadline passed; stopping the unit" >&2; stop_unit; break
  fi
  sleep 1
done

RES=$(systemctl --user show -p Result --value "$UNIT")
CODE=$(cat "$OUT/exitcode" 2>/dev/null || echo none)
# a unit that ended without the command's exit code was killed (limit, timeout)
[ "$CODE" = none ] && [ "$RES" = success ] && RES=killed-no-exit-code
[ "$CODE" != 0 ] && [ "$RES" = success ] && RES=exit-code
{
  echo "result=$RES"; echo "exit=$CODE"
  echo "memory_peak_file=$(cat "$OUT/peak.last" 2>/dev/null)"
  echo "memory_current_max_sampled=$PEAKSEEN"; echo "max_concurrent_lean=$MAXPROCS"
  echo "events: $(tr '\n' ' ' < "$OUT/events.last" 2>/dev/null)"
} > "$OUT/result.txt"
systemctl --user reset-failed "$UNIT" 2>/dev/null
rm -f "$ROOT/.current"
trap - INT TERM HUP
echo "== $OUT"; cat "$OUT/protect.txt" "$OUT/result.txt"
[ "$RES" = success ] && exit 0
[ "$RES" = oom-kill ] && exit 137
[ "$RES" = timeout ] && exit 124
[ "$CODE" = none ] && exit 1
exit "$CODE"
