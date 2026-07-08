#!/usr/bin/env bash
# RAM-watchdog exec wrapper: run a command under a hard, kernel-enforced
# memory cap.
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# The command runs in a fresh cgroup (v2) with `memory.max` at the
# ceiling: the kernel caps the tree's RESIDENT memory and, with
# `memory.oom.group`, OOM-kills the whole group atomically at the line,
# exiting 137. This charges actual pages (an allocator's cached virtual
# reservations can't false-trip it), sums the entire process tree
# (Zisk's ASM microservices), and can't lose a race (no sampling — a
# prover's commit phases allocate multiple GB/s).
#
# Requires cgroup v2 and passwordless sudo (both present on the CI
# runners and any modern Linux box). NO FALLBACK: a run whose ceiling
# can't be enforced is not a benchmark run — fail loudly instead.
#
# Exits with the child's status (137 after an OOM kill). That is the
# whole job: no markers, no exit-code taxonomy, no output parsing. The
# orchestrator (`ix bench run`) treats any exit ≥128 as the in-flight
# constant's OOM.
set -uo pipefail

ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }

die() { echo "watchdog: $1 — cannot enforce the ${ceiling_gb}G ceiling; refusing to run unguarded" >&2; exit 2; }

[ -f /sys/fs/cgroup/cgroup.controllers ] || die "no cgroup v2 at /sys/fs/cgroup"
grep -qw memory /sys/fs/cgroup/cgroup.controllers || die "cgroup v2 memory controller unavailable"
command -v sudo >/dev/null && sudo -n true 2>/dev/null || die "no passwordless sudo"

cg="/sys/fs/cgroup/ixbench-$$"
sudo mkdir "$cg" || die "mkdir $cg failed"
echo $((ceiling_gb * 1024 * 1024 * 1024)) | sudo tee "$cg/memory.max" >/dev/null \
  || die "writing memory.max failed"
echo 1 | sudo tee "$cg/memory.oom.group" >/dev/null \
  || die "writing memory.oom.group failed"
# Absent when swap accounting is off (then there is no swap to escape to).
echo 0 | sudo tee "$cg/memory.swap.max" >/dev/null 2>&1 || true

echo "watchdog: cgroup memory.max=${ceiling_gb}G ($cg)" >&2
(
  echo "$BASHPID" | sudo tee "$cg/cgroup.procs" >/dev/null || exit 2
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
