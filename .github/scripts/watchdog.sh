#!/usr/bin/env bash
# RAM-watchdog exec wrapper: kill a command's process tree before the
# MACHINE runs out of memory.
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# One signal, read from the kernel: /proc/meminfo MemAvailable — the
# kernel's own estimate of what can still be allocated without thrashing.
# It already accounts for everything the tree consumes (RSS, locked shared
# memory, page tables) plus everything else on the host, and correctly
# ignores reclaimable page cache. The kill floor is MemTotal - ceiling:
# the tree may use up to <ceiling_gb>, and anything driving available
# memory below the remainder trips a TERM -> 2s -> KILL of the tree.
# Sampling is a fixed 0.25s (a meminfo read is ~free); the headroom baked
# into the default ceiling absorbs the worst measured burst (a prover
# first-touching pre-reserved buffers moves ~13 GB per sample). The floor
# never drops below 4 GiB, so a ceiling at or above machine RAM still
# protects the host. Linux-only by design (no /proc/meminfo -> refuse).
#
# Exits with the child's status (143/137 after a kill). That is the whole
# job: no markers, no exit-code taxonomy, no output parsing. The
# orchestrator (`ix bench run`) treats any exit >=128 - these kills or
# the kernel OOM killer's - as the in-flight constant's OOM.
set -uo pipefail

ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }

mem_total_kb=$(awk '/^MemTotal:/{print $2}' /proc/meminfo 2>/dev/null)
[ -n "$mem_total_kb" ] || { echo "watchdog: no /proc/meminfo; cannot enforce a ceiling" >&2; exit 2; }
floor_kb=$(( mem_total_kb - ceiling_gb * 1024 * 1024 ))
min_floor_kb=$(( 4 * 1024 * 1024 ))
[ "$floor_kb" -lt "$min_floor_kb" ] && floor_kb=$min_floor_kb

"$@" &
root=$!

tree_pids() {  # every live pid in root's descendant tree, root included
  ps -eo pid,ppid --no-headers 2>/dev/null | awk -v root="$root" '
    { parent[$1]=$2 }
    END {
      alive[root]=1; changed=1
      while (changed) {
        changed=0
        for (p in parent) if (alive[parent[p]] && !alive[p]) { alive[p]=1; changed=1 }
      }
      for (p in alive) print p
    }'
}

(
  while kill -0 "$root" 2>/dev/null; do
    avail_kb=$(awk '/^MemAvailable:/{print $2}' /proc/meminfo)
    if [ -n "$avail_kb" ] && [ "$avail_kb" -lt "$floor_kb" ]; then
      echo "watchdog: MemAvailable ${avail_kb}kB < floor ${floor_kb}kB (ceiling ~${ceiling_gb} GB); killing pid=$root tree" >&2
      kill -TERM $(tree_pids) 2>/dev/null
      sleep 2
      kill -KILL $(tree_pids) 2>/dev/null
      exit 0
    fi
    sleep 0.25
  done
) &
monitor=$!

wait "$root"
status=$?
kill "$monitor" 2>/dev/null
wait "$monitor" 2>/dev/null
exit "$status"
