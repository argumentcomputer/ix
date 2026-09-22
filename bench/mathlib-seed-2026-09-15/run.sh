#!/bin/sh
# run.sh RUNDIR: one `ix prove --lanes` Mathlib run under a cgroup cap, with
# everything the shard-count calibration needs recorded beside it
# (docs/aiur-multi-gpu-design.md §7 item 4). Set IX, IXE and IXES; RUNDIR
# must not exist. LANES, EXEC_JOBS, MAX_RAM and CAP override the runbook's.
#
#   IX=~/repos/ix/.lake/build/bin/ix IXE=mathlib.ixe IXES=mathlib-seed-230.ixes \
#     sh run.sh seed111-run1
#
# Uses a fresh AIUR_LANES_CACHE_DIR under RUNDIR so nothing resumes from an
# earlier run and every claim and join is executed and measured; the store
# (~/.ix/store) is shared and content-addressed, so that is safe.
set -eu
RUNDIR=${1:?run directory}
: "${IX:?set IX}" "${IXE:?set IXE}" "${IXES:?set IXES}"
LANES=${LANES:-4} EXEC_JOBS=${EXEC_JOBS:-3} MAX_RAM=${MAX_RAM:-230} CAP=${CAP:-920G}
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_TRACE_SHARD_MAX_CELLS=${AIUR_TRACE_SHARD_MAX_CELLS:-1500000000}
export AIUR_GPU_TRACE=${AIUR_GPU_TRACE:-cpu} AIUR_TREE_CACHE_BYTES=${AIUR_TREE_CACHE_BYTES:-0}
export LC_ALL=C
[ -e "$RUNDIR" ] && { echo "$RUNDIR exists" >&2; exit 1; }
mkdir -p "$RUNDIR/cache"
export AIUR_LANES_CACHE_DIR=$(cd "$RUNDIR/cache" && pwd)
{
  echo "started $(date -u +%FT%TZ)"
  echo "host $(hostname) $(uname -r)"
  echo "ix $(sha256sum "$IX")"
  echo "ixe $(sha256sum "$IXE")"
  echo "ixes $(sha256sum "$IXES")"
  echo "nvcc $(nvcc --version | tail -1)"
  echo "driver $(nvidia-smi --query-gpu=driver_version --format=csv,noheader | head -1)"
  echo "thp $(cat /sys/kernel/mm/transparent_hugepage/enabled) / $(cat /sys/kernel/mm/transparent_hugepage/defrag)"
  echo "cpus $(nproc)  mem $(free -g | awk '/^Mem/{print $2}') GiB"
  echo "flags --lanes $LANES --exec-jobs $EXEC_JOBS --max-ram $MAX_RAM  cap $CAP"
  env | grep -E '^(AIUR_|MULTI_STARK_|RAYON_|CUDA_)' | sort
  for repo in "${IX_REPO:-$HOME/repos/ix}" "${MS_REPO:-$HOME/repos/multi-stark}"; do
    echo "$(basename "$repo") git $(git -C "$repo" rev-parse HEAD) $(git -C "$repo" status --porcelain | wc -l) dirty files"
  done
  # A frozen build's provenance (its build.json and source patches), when the
  # binary came from one of the bench build scripts.
  for f in "$(dirname "$IX")"/build.json "$(dirname "$IX")"/*.patch; do
    [ -f "$f" ] && echo "build file $(sha256sum "$f")"
  done
} > "$RUNDIR/meta.txt"
nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw \
  --format=csv,noheader -l 1 > "$RUNDIR/gpu.csv" 2>/dev/null &
SMI=$!
trap 'kill $SMI 2>/dev/null' EXIT INT TERM
set +e
systemd-run --user --scope -q -p MemoryMax="$CAP" -- \
  /usr/bin/time -v "$IX" prove --ixe "$IXE" --ixes "$IXES" --trace-shards \
    --lanes "$LANES" --exec-jobs "$EXEC_JOBS" --max-ram "$MAX_RAM" \
    > "$RUNDIR/lanes.out" 2> "$RUNDIR/lanes.err"
status=$?
set -e
echo "exit $status" >> "$RUNDIR/meta.txt"
echo "ended $(date -u +%FT%TZ)" >> "$RUNDIR/meta.txt"
kill $SMI 2>/dev/null || true
echo "exit $status; root: $(cat "$RUNDIR/lanes.out")"
exit $status
