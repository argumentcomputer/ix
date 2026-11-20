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
short_of_memory() {
  [ "$(awk '/^MemAvailable:/ { print int($2 / 1048576) }' /proc/meminfo)" -lt "$min_free" ]
}
exec 8>"$lock"
flock 8
while same_dir_lake || short_of_memory; do
  echo "$(date +%T) light-waiting: $what" >> "$log"; sleep 10
done
echo "$(date +%T) light-start ($(free -g | awk 'NR==2{print $7}')G available): $what" >> "$log"
status=0
systemd-run --user --scope -q -p MemoryMax="${mem}G" -p MemorySwapMax=0 -- timeout "$cap" "$@" || status=$?
echo "$(date +%T) light-end ($status): $what" >> "$log"
exit $status
