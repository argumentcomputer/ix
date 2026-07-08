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

exec systemd-run --user --scope --quiet \
  -p MemoryMax="${ceiling_gb}G" -p MemorySwapMax=0 \
  "$@"
