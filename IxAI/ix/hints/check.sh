#!/usr/bin/env bash
# check.sh ENV.ixe LOG NAME... : IxVM execution (no proof) of the named claims, memory-capped.
set -u
ixe=$1; log=$2; shift 2
exec > "$log" 2>&1
/usr/bin/time -v systemd-run --user --scope -q -p MemoryMax=180G -- \
  timeout 7200 /home/sam/repos/ix-ai-pipeline/ix/ixw check --ixe "$ixe" --keep-going "$@"
