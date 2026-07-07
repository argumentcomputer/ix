#!/usr/bin/env bash
# RAM-watchdog exec wrapper: run a command, kill its tree before it takes
# the machine down.
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# Runs <cmd> as a child and every ~3s sums RSS across it and every
# descendant. On breach, SIGTERM the whole tree, wait up to 10s for a
# graceful exit (tools flush their in-flight results row and run
# destructors — e.g. Zisk's shm cleanup), then SIGKILL whatever survives.
# Exits with the child's status (143/137 after a watchdog kill).
#
# That is the whole job: no markers, no exit-code taxonomy, no output
# parsing. The orchestrator (`ix bench run`) infers "killed" from the
# abnormal exit and the results file's missing row, and treats a kernel
# OOM-killer SIGKILL (exit 137) — which a fast spike can reach before the
# 3s cadence does — identically.
set -uo pipefail

ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }
max_kb=$((ceiling_gb * 1024 * 1024))

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
      for _ in $(seq 10); do
        kill -0 "$root" 2>/dev/null || exit 0
        sleep 1
      done
      echo "watchdog: grace expired; KILL" >&2
      kill -KILL $(tree_pids) 2>/dev/null
      exit 0
    fi
    sleep 3
  done
) &
monitor=$!

wait "$root"
status=$?
kill "$monitor" 2>/dev/null
wait "$monitor" 2>/dev/null
exit "$status"
