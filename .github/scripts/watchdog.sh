#!/usr/bin/env bash
# Hard memory cap: run <cmd> in a systemd user scope with cgroup-v2
# memory.max = <ceiling_gb> and swap disabled. The kernel OOM-kills at
# the cap — SIGKILL, exit 137, which the orchestrator (`ix bench run`)
# reads as the in-flight constant's OOM. No sampler to race, nothing to
# sum: the cgroup charges the whole tree's resident memory, and cached
# allocator reservations don't count. Validated on ubuntu-latest and
# warp runners (see ix-cpu-info's cgroup-memcap.yml).
#
#   watchdog.sh <ceiling_gb> <cmd> [args...]
#
# Needs a user systemd instance: the linger call boots one on CI
# (passwordless sudo); it no-ops locally, where a desktop session
# already provides the user manager.
set -u
ceiling_gb=${1:?ceiling_gb}
shift
[ $# -ge 1 ] || { echo "watchdog: no command given" >&2; exit 2; }

sudo -n loginctl enable-linger "${USER:-$(id -un)}" 2>/dev/null || true
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$(id -u)}

# memory.oom.group=1: on breach the kernel kills the WHOLE scope (exit
# 137 -> oom row), not just its biggest process. Without it, Zisk's ASM
# service gets singled out and the surviving host converts the memory
# kill into a clean exit 1 — which the orchestrator must treat as a
# deterministic failure. The scope's cgroup is user-delegated, so the
# write needs no sudo; if it fails, exit 2 rather than run with wrong
# kill semantics.
exec systemd-run --user --scope --quiet \
  -p MemoryMax="${ceiling_gb}G" -p MemorySwapMax=0 \
  bash -c 'echo 1 > "/sys/fs/cgroup$(cut -d: -f3- /proc/self/cgroup)/memory.oom.group" \
             || { echo "watchdog: cannot set memory.oom.group" >&2; exit 2; }
           exec "$@"' watchdog "$@"
