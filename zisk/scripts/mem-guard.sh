#!/usr/bin/env bash
# Shared memory watchdog for the Zisk prove scripts. Source this file, then
# wrap the prover with `run_guarded`:
#
#   source "$(dirname "${BASH_SOURCE[0]}")/mem-guard.sh"
#   run_guarded cargo run --release --bin zisk-host -- --gpu --ixe ...
#
# `run_guarded` launches the command in the background and starts a watcher
# that polls system memory every MEM_GUARD_INTERVAL seconds. If used RAM
# (MemTotal - MemAvailable, i.e. memory the kernel can't reclaim — the
# metric that actually predicts OOM) exceeds MEM_LIMIT_GIB, it SIGKILLs the
# command's process subtree (cargo + zisk-host) before the kernel OOM killer
# or swap thrash kicks in.
#
# Tunables (env vars):
#   MEM_LIMIT_GIB=200     trip threshold in GiB (200 GiB ≈ 215 GB; the box has
#                         256 GB, so this leaves ~40 GB margin). Lower it for a
#                         tighter safety bound.
#   MEM_GUARD_INTERVAL=2  poll period in seconds.
#
# Exit status: the command's own status, or 137 (128+SIGKILL) if the guard
# tripped. There is NO checkpointing — a kill loses in-flight shard proofs,
# so the run restarts from the first shard.

run_guarded() {
  local limit_gib="${MEM_LIMIT_GIB:-200}"
  local interval="${MEM_GUARD_INTERVAL:-2}"
  local limit_kb=$(( limit_gib * 1024 * 1024 ))

  echo "[mem-guard] active: will SIGKILL the prover if used RAM exceeds ${limit_gib} GiB (poll ${interval}s)" >&2

  "$@" &
  local cmd_pid=$!

  (
    # Subshell watcher. Plain vars (no `local` — not in a function here).
    while kill -0 "$cmd_pid" 2>/dev/null; do
      used_kb=$(awk '/^MemTotal:/{t=$2} /^MemAvailable:/{a=$2} END{print t-a}' /proc/meminfo)
      if [ "$used_kb" -gt "$limit_kb" ]; then
        echo "[mem-guard] used $((used_kb/1024/1024)) GiB > ${limit_gib} GiB limit — killing prover (pid ${cmd_pid}) and zisk-host" >&2
        pkill -9 -P "$cmd_pid" 2>/dev/null || true   # direct children of cargo (the zisk-host bin)
        kill -9 "$cmd_pid" 2>/dev/null || true        # cargo itself
        pkill -9 -x zisk-host 2>/dev/null || true     # belt-and-suspenders
        exit 0
      fi
      sleep "$interval"
    done
  ) &
  local guard_pid=$!

  # `set -e` safety: `wait` on a killed child returns non-zero; capture it
  # without letting it abort the script so cleanup + status reporting run.
  local status=0
  wait "$cmd_pid" || status=$?
  # Prover finished (or was killed) — stop the watcher.
  kill "$guard_pid" 2>/dev/null || true
  wait "$guard_pid" 2>/dev/null || true
  if [ "$status" -ne 0 ]; then
    echo "[mem-guard] prover exited with status ${status}$( [ "$status" -eq 137 ] && echo ' (SIGKILL — likely the mem-guard tripped)' )" >&2
  fi
  return "$status"
}
