#!/usr/bin/env bash
# Run a heavy command (proving, compression, large compiles) only when the machine is free.
#
# It waits until no other build or prover is running (lake, lean, cargo, rustc, nvcc, ix prove,
# ix compress, lane's elaborating commands) and the 1-minute load average is below MAX_LOAD (default 8 of 32 cores), then takes
# the heavy-job lock that other sessions on this machine use, re-checks under the lock, and runs
# the command. Every decision is logged to .truthmines/heavy.log.
#   heavy.sh COMMAND [ARGS...]
set -euo pipefail
what="$(printf '%s ' "$@" | cut -c1-160)"
here="$(cd "$(dirname "$0")" && pwd)"
log="$(dirname "$here")/.truthmines/heavy.log"
# The lock is shared with every other session on the machine, so its default is one fixed path;
# HEAVY_LOCK overrides it on a machine laid out differently.
lock="${HEAVY_LOCK:-/home/sam/repos/ix.aiur-compression-active/target/heavy.lock}"
max_load="${MAX_LOAD:-8}"
mkdir -p "$(dirname "$log")"
# Inside a PID-namespace sandbox `ps` sees only the sandbox's own processes, and the machine
# would look free when it is not. Refuse rather than guess.
if [ "$(ps -e --no-headers | wc -l)" -lt 50 ]; then
  echo "heavy.sh: cannot see the machine's processes (sandboxed?); refusing to run: $what" >&2
  exit 3
fi
# The callers of this script (e.g. `lane submit` running its validation through the gate) match
# the busy pattern themselves; counting them would make the job wait on itself forever.
ancestors=" "
p=$PPID
while [ -n "$p" ] && [ "$p" -gt 1 ]; do
  ancestors="$ancestors$p "
  p=$(ps -o ppid= -p "$p" | tr -d ' ')
done
busy() {
  # Other heavy processes, excluding this script's own process tree and its callers.
  local others
  # Shells and other wrappers are not work: a script that retries a light job has the build's
  # words on its command line for as long as it waits.
  others=$(ps -eo pid,ppid,comm,args | awk -v self=$$ -v anc="$ancestors" \
      '$1 != self && $2 != self && index(anc, " " $1 " ") == 0 &&
       $3 !~ /^(bash|sh|dash|zsh|timeout|time|sleep|flock|tee|env|systemd-run|python3?|awk|sed|tail|cat)$/ {
         $3 = ""; print }' \
    | grep -E '(/|\s)(lake build|lean |cargo build|rustc |nvcc|ix (prove|compress|aggregate)|lane (prove|prove-session|verify|submit|check|merge))' \
    | grep -v -E 'grep|heavy\.sh|light\.sh' \
    | awk '$3 != "flock" && $3 !~ /\/flock$/' \
    | while read -r pid rest; do
        grep -q 'ixai-light' "/proc/$pid/cgroup" 2>/dev/null || echo "$pid $rest"
      done || true)
  # Jobs of the light lane (light.sh, in scopes named ixai-light-…) run beside heavy jobs by
  # design and are not waited for.
  # A `flock LOCK cmd` process is waiting for the lock this script may hold, not running `cmd`;
  # counting it as busy would deadlock both sides.
  local load; load=$(cut -d' ' -f1 /proc/loadavg)
  if [ -n "$others" ]; then echo "busy: $(echo "$others" | head -1 | cut -c1-120)"; return 0; fi
  if awk -v l="$load" -v m="$max_load" 'BEGIN { exit !(l >= m) }'; then echo "busy: load $load"; return 0; fi
  return 1
}
# First come, first served: a waiter proceeds only when its ticket is the oldest, so a job that
# runs many heavy steps back to back cannot starve the others.
queue="$(dirname "$log")/heavy.queue"
mkdir -p "$queue"
# HEAVY_PRIORITY=N (N >= 1) queues the job ahead of every waiting job with a lower priority: its
# ticket carries N leading zeros and sorts first. For a measurement that other work is waiting
# on, not for routine jobs.
ticket="$queue/$(printf '%*s' "${HEAVY_PRIORITY:-0}" '' | tr ' ' 0)$(date +%s%N).$$"
: > "$ticket"
trap 'rm -f "$ticket"' EXIT
oldest() {
  local t
  for t in $(ls "$queue" | sort); do
    if kill -0 "${t##*.}" 2>/dev/null; then [ "$queue/$t" = "$ticket" ]; return; fi
    rm -f "$queue/$t"
  done
  return 1
}
# The lock is taken inside the loop, never waited for: a job that left the queue to wait for the
# lock would start next whatever arrived meanwhile, and a job with a higher priority could not
# pass it. (The running job need not look busy: not every heavy command matches the patterns.)
exec 9>"$lock"
until oldest && ! reason=$(busy) && flock -n 9; do
  if ! oldest; then reason="queued behind an earlier heavy job"
  elif [ -z "${reason:-}" ]; then reason="the heavy lock is held"; fi
  echo "$(date +%T) waiting ($reason): $what" >> "$log"; reason=""; sleep 15
done
while reason=$(busy); do
  echo "$(date +%T) waiting under lock ($reason): $what" >> "$log"; sleep 30
done
echo "$(date +%T) start (load $(cut -d' ' -f1 /proc/loadavg), $(free -g | awk 'NR==2{print $7}')G available): $what" >> "$log"
rm -f "$ticket"
# A failing command must still reach the end line: waiters key on it.
status=0
"$@" || status=$?
echo "$(date +%T) end ($status): $what" >> "$log"
exit $status
