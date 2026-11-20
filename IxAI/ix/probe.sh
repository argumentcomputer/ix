#!/usr/bin/env bash
# Time IxVM execution (no proving) of selected constants, each capped at CAP seconds.
#   probe.sh ENV.ixe NAME...
here="$(cd "$(dirname "$0")" && pwd)"
env="$1"; shift
for n in "$@"; do
  start=$(date +%s)
  timeout "${CAP:-300}" env IX_PROFILE=ci-pinned "$here/ixw" check --ixe "$env" "$n" > /dev/null 2>&1
  status=$?
  echo "$n: exit $status after $(( $(date +%s) - start ))s$([ $status = 124 ] && echo ' (timed out)')"
done
