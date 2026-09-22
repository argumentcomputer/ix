#!/bin/bash
# prove-distributed.sh IXE IXES MAX_RAM_GIB CELLS [EXEC_JOBS] [extra ix args...]
# Runs the distributed prove; on a kill by the memory cap (exit 137) retries
# with the execution concurrency halved, down to 1. Wrap the whole script in
# a cgroup scope for the hard cap, e.g.
#   systemd-run --scope -p MemoryMax=230G -- ./prove-distributed.sh ...
set -u
IXE=$1; IXES=$2; RAM=$3; CELLS=$4; JOBS=${5:-$(nproc)}; shift 5 2>/dev/null || shift $#
IX=${IX:-ix}
while :; do
  echo "[prove-distributed] --exec-jobs $JOBS --max-ram $RAM"
  $IX prove --ixe "$IXE" --ixes "$IXES" --distributed --cells "$CELLS" --max-ram "$RAM" --exec-jobs "$JOBS" "$@"
  code=$?
  [ $code -ne 137 ] && exit $code
  [ "$JOBS" -le 1 ] && { echo "[prove-distributed] killed by the memory cap at one execution at a time; use smaller chunks"; exit 137; }
  JOBS=$((JOBS / 2))
  echo "[prove-distributed] killed by the memory cap; retrying with --exec-jobs $JOBS"
done
