#!/usr/bin/env bash
# Run a light command without waiting in the heavy-job queue.
#
# Light means: a build or check of a few of this project's own Lean modules, one compile of its
# CUDA shim, a seconds-long identity check on a small input, or a script that only reads results.
# Never proving, IxVM execution, compression, a build of ix or of a Rust crate, anything that
# uses the GPU, a test suite that runs a prover or a checker, or anything whose timing is
# reported; those go through heavy.sh.
#
# A light job does not take the heavy-job lock, so it can run beside a heavy job. What keeps that
# safe: light jobs run one at a time; each runs in a scope capped at LIGHT_MEM GiB (default 24),
# so it cannot take memory from a prover; it starts only when LIGHT_MIN_FREE GiB (default 48) are
# available; it is stopped after LIGHT_CAP seconds (default 900); and it waits while another
# `lake` works in the same directory. Its start and end are logged to .truthmines/heavy.log as
# `light-start` and `light-end`, so an overlap with a timed heavy job is visible there.
#
# Light jobs must not hold up the heavy queue. heavy.sh does not wait for them: it recognizes
# them by their scope name (`ixai-light-…`) and by this script's name on the command line. A
# heavy job queued by a copy of heavy.sh older than that rule still waits for a moment with no
# build process at all, and even a waiting light job's command line counts against it. While
# such a job is next in the queue and no heavy job is running, this script therefore exits at
# once with status 75 and asks the caller to retry, instead of waiting.
#   light.sh COMMAND [ARGS...]
set -euo pipefail
what="$(printf '%s ' "$@" | cut -c1-160)"
here="$(cd "$(dirname "$0")" && pwd)"
log="$(dirname "$here")/.truthmines/heavy.log"
lock="$(dirname "$here")/.truthmines/light.lock"
mem="${LIGHT_MEM:-24}"
min_free="${LIGHT_MIN_FREE:-48}"
cap="${LIGHT_CAP:-900}"
mkdir -p "$(dirname "$log")"
# The memory scope needs the user's systemd session, which a sandboxed command cannot reach.
if [ "$(ps -e --no-headers | wc -l)" -lt 50 ]; then
  echo "light.sh: cannot see the machine's processes (sandboxed?); refusing to run: $what" >&2
  exit 3
fi
same_dir_lake() {
  local pid
  for pid in $(pgrep -x lake || true); do
    if [ "$(readlink "/proc/$pid/cwd" 2>/dev/null)" = "$PWD" ]; then return 0; fi
  done
  return 1
}
queue="$(dirname "$log")/heavy.queue"
heavy_lock="${HEAVY_LOCK:-/home/sam/repos/ix.aiur-compression-active/target/heavy.lock}"
# True when the next heavy job to start was queued by a heavy.sh that waits for light jobs (its
# ticket, named by its creation time in nanoseconds, is older than the current heavy.sh) and no
# heavy job is running.
old_heavy_about_to_start() {
  local t head=""
  for t in $(ls "$queue" 2>/dev/null | sort); do
    if kill -0 "${t##*.}" 2>/dev/null; then head=$t; break; fi
  done
  # The last start or end line says whether a heavy job is running now.
  case "$(tac "$log" 2>/dev/null | grep -m1 -E '^[0-9:]+ (start|end) ')" in
    *" start "*) return 1 ;;
  esac
  # A job that holds the heavy lock without having started is waiting, under the lock, for the
  # same quiet moment, whatever its place in the queue.
  flock -n "$heavy_lock" true 2>/dev/null || return 0
  [ -n "$head" ] || return 1
  [ "${head%%.*}" -lt "$(stat -c %Y "$here/heavy.sh")000000000" ] || return 1
  return 0
}
stand_aside() {
  echo "$(date +%T) light-deferred: $what" >> "$log"
  echo "light.sh: a heavy job is about to start and needs a quiet moment; nothing was run. Retry in 30 seconds: $what" >&2
  exit 75
}
old_heavy_about_to_start && stand_aside
short_of_memory() {
  [ "$(awk '/^MemAvailable:/ { print int($2 / 1048576) }' /proc/meminfo)" -lt "$min_free" ]
}
exec 8>"$lock"
flock 8
while same_dir_lake || short_of_memory; do
  echo "$(date +%T) light-waiting: $what" >> "$log"; sleep 10
done
old_heavy_about_to_start && stand_aside
echo "$(date +%T) light-start ($(free -g | awk 'NR==2{print $7}')G available): $what" >> "$log"
status=0
systemd-run --user --scope -q --unit="ixai-light-$$-$(date +%s)" -p MemoryMax="${mem}G" -p MemorySwapMax=0 -- \
  timeout "$cap" "$@" || status=$?
echo "$(date +%T) light-end ($status): $what" >> "$log"
exit $status
