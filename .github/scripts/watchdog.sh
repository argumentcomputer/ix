#!/usr/bin/env bash
# RAM-watchdog exec wrapper: run a command, kill its tree before it takes
# the machine down.
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# Two enforcement layers:
#
# 1. RLIMIT_DATA at the ceiling on the spawned command: the allocation
#    that would cross the line FAILS inside the process — Rust's
#    handle_alloc_error / Lean's OOM panic abort on the spot (SIGABRT,
#    exit 134) with zero overshoot. This is the primary defense: a
#    prover's commit phases allocate multiple GB/s across 32 threads,
#    which no sampling cadence can catch before the VM is thrashing
#    (observed: 13 GB past the ceiling within one sample; the runner
#    agent misses its heartbeat and GitHub cancels the job before any
#    kill lands). The limit is per-process; anonymous allocations count,
#    file-backed mmaps don't.
# 2. A ~1s tree-RSS sampler as backstop for what RLIMIT_DATA can't see:
#    the SUM across a multi-process tree (Zisk's ASM microservices).
#    On breach, SIGTERM the tree, then re-sample each second — the
#    grace (up to 10s, for destructors) only continues while the tree
#    is BELOW the ceiling; still at/above means still allocating →
#    SIGKILL immediately. Tools flush results rows as they go, so
#    nothing of value needs the grace.
#
# Exits with the child's status (134/143/137 after a limit/kill). That
# is the whole job: no markers, no exit-code taxonomy, no output
# parsing. The orchestrator (`ix bench run`) treats any exit ≥128 —
# this script's aborts and kills, or the kernel OOM killer's — as the
# in-flight constant's OOM.
set -uo pipefail

ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }
max_kb=$((ceiling_gb * 1024 * 1024))

(
  ulimit -d "$max_kb" 2>/dev/null || true
  exec "$@"
) &
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

tree_rss_kb() {
  ps -eo pid,ppid,rss --no-headers 2>/dev/null | awk -v root="$root" '
    { rss[$1]=$3; parent[$1]=$2 }
    END {
      alive[root]=1; changed=1
      while (changed) {
        changed=0
        for (p in parent) if (alive[parent[p]] && !alive[p]) { alive[p]=1; changed=1 }
      }
      s=0; for (p in alive) s += rss[p]+0
      print s
    }'
}

(
  while kill -0 "$root" 2>/dev/null; do
    total_kb=$(tree_rss_kb)
    if [ -n "$total_kb" ] && [ "$total_kb" -gt "$max_kb" ]; then
      echo "watchdog: tree-RSS ${total_kb}kB > ${max_kb}kB (~${ceiling_gb} GB); TERM pid=$root tree" >&2
      pids=$(tree_pids)
      kill -TERM $pids 2>/dev/null
      for _ in $(seq 10); do
        sleep 1
        kill -0 "$root" 2>/dev/null || exit 0
        total_kb=$(tree_rss_kb)
        if [ -n "$total_kb" ] && [ "$total_kb" -gt "$max_kb" ]; then
          echo "watchdog: still ${total_kb}kB above ceiling after TERM; KILL now" >&2
          kill -KILL $(tree_pids) 2>/dev/null
          exit 0
        fi
      done
      echo "watchdog: grace expired; KILL" >&2
      kill -KILL $(tree_pids) 2>/dev/null
      exit 0
    fi
    sleep 1
  done
) &
monitor=$!

wait "$root"
status=$?
kill "$monitor" 2>/dev/null
wait "$monitor" 2>/dev/null
exit "$status"
