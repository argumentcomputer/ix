#!/usr/bin/env bash
# RAM-watchdog exec wrapper: run a command, kill its tree before it takes
# the machine down.
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# Samples the process tree's summed RSS and kills the tree on breach.
# Adaptive cadence: ~1s normally, dropping to 0.2s once the tree is
# within 20 GB of the ceiling (100 GB at the default 120) — the danger
# zone where a prover's commit phases can allocate multiple GB/s and a
# relaxed cadence would let the breach outrun the kill. On breach,
# SIGTERM the tree, then re-sample every 0.2s: the grace (up to 10s,
# for destructors — e.g. Zisk's shm cleanup) only continues while the
# tree is BELOW the ceiling; still at/above means still allocating →
# SIGKILL immediately. Tools flush results rows as they go, so nothing
# of value needs the grace.
#
# Exits with the child's status (143/137 after a kill). That is the
# whole job: no markers, no exit-code taxonomy, no output parsing. The
# orchestrator (`ix bench run`) treats any exit ≥128 — this script's
# kills or the kernel OOM killer's — as the in-flight constant's OOM.
set -uo pipefail

ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }
max_kb=$((ceiling_gb * 1024 * 1024))
# Fast-sampling zone: within 20 GB of the ceiling.
fast_kb=$(( ceiling_gb > 20 ? (ceiling_gb - 20) * 1024 * 1024 : 0 ))

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
      for _ in $(seq 50); do
        sleep 0.2
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
    if [ -n "$total_kb" ] && [ "$total_kb" -gt "$fast_kb" ]; then
      sleep 0.2
    else
      sleep 1
    fi
  done
) &
monitor=$!

wait "$root"
status=$?
kill "$monitor" 2>/dev/null
wait "$monitor" 2>/dev/null
exit "$status"
