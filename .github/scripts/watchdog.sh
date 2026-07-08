#!/usr/bin/env bash
# RAM-watchdog exec wrapper: run a command, kill its tree before it takes
# the machine down.
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# Preferred mode — cgroup v2 `memory.max` (needs cgroup v2 + passwordless
# sudo, both true on the CI runners): the kernel caps the tree's RESIDENT
# memory and OOM-kills the whole group atomically at the ceiling
# (memory.oom.group), exiting 137. This is the real primitive the
# fallbacks approximate: it charges actual pages (an allocator's cached
# virtual reservations don't count, so Lean's mimalloc slack can't
# false-trip it), it sums the whole tree (Zisk's ASM microservices), and
# it can't lose a race (no sampling — a prover's commit phases allocate
# multiple GB/s, faster than any sampler reacts).
#
# Fallback (no cgroup/sudo — local runs), two layers:
# 1. RLIMIT_DATA at the ceiling: the over-budget allocation FAILS inside
#    the process (Rust handle_alloc_error → SIGABRT 134; Lean OOM panic).
#    Caveat: it caps VIRTUAL data mappings, which allocator caching can
#    push far above true RSS — big Lean-env workloads may trip it early.
# 2. A ~1s tree-RSS sampler for the multi-process sum: on breach, SIGTERM
#    the tree, re-sample each second (grace only continues while BELOW
#    the ceiling; still above → SIGKILL now).
#
# Exits with the child's status (137/134/143 after a kill/limit). That
# is the whole job: no markers, no exit-code taxonomy, no output
# parsing. The orchestrator (`ix bench run`) treats any exit ≥128 —
# these kills or the kernel OOM killer's — as the in-flight constant's
# OOM.
set -uo pipefail

ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }
max_kb=$((ceiling_gb * 1024 * 1024))

cg=""
if [ -f /sys/fs/cgroup/cgroup.controllers ] \
    && grep -qw memory /sys/fs/cgroup/cgroup.controllers \
    && command -v sudo >/dev/null && sudo -n true 2>/dev/null \
    && sudo mkdir "/sys/fs/cgroup/ixbench-$$" 2>/dev/null; then
  cg="/sys/fs/cgroup/ixbench-$$"
  echo $((ceiling_gb * 1024 * 1024 * 1024)) | sudo tee "$cg/memory.max" >/dev/null
  echo 0 | sudo tee "$cg/memory.swap.max" >/dev/null 2>&1 || true
  echo 1 | sudo tee "$cg/memory.oom.group" >/dev/null
fi

if [ -n "$cg" ]; then
  echo "watchdog: cgroup memory.max=${ceiling_gb}G ($cg)" >&2
  (
    echo "$BASHPID" | sudo tee "$cg/cgroup.procs" >/dev/null
    exec "$@"
  ) &
  root=$!
  wait "$root"
  status=$?
  if grep -Eq 'oom_kill [1-9]' "$cg/memory.events" 2>/dev/null; then
    echo "watchdog: kernel OOM-killed the tree at memory.max=${ceiling_gb}G" >&2
  fi
  # Reap any stragglers still charged to the group, then remove it.
  echo 1 | sudo tee "$cg/cgroup.kill" >/dev/null 2>&1 || true
  sudo rmdir "$cg" 2>/dev/null || true
  exit "$status"
fi

echo "watchdog: no cgroup v2 + sudo; falling back to RLIMIT_DATA + sampler" >&2
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
