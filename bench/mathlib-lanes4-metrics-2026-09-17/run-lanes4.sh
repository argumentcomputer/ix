#!/bin/bash
# Mathlib on four GPU lanes with lightweight metrics (docs/aiur-lightweight-metrics.md).
# Usage: run-lanes4.sh <label> [extra ix prove flags]
set -u
LABEL=$1; shift
EXEC_JOBS=${EXEC_JOBS:-3}
BIN=$HOME/repos/ix/.lake/build/bin/ix
D=$HOME/benchdata/mathlib; OUT=$D/runs/$LABEL
mkdir -p "$OUT/cache" || exit 1
cd "$D" || exit 1
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000
export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$OUT/cache
export AIUR_METRICS=$OUT/metrics.jsonl AIUR_METRICS_RUN_ID=$LABEL
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
unset AIUR_PROFILE AIUR_CUDA_PROFILE CUDA_INJECTION64_PATH RUST_LOG MULTI_STARK_CUDA_MEMORY_LOG
{
  echo "started $(date -u +%FT%TZ)"; echo "host $(hostname) $(uname -r)"
  echo "ix $(sha256sum "$BIN" | cut -d' ' -f1)"; echo "ixe $(sha256sum mathlib.ixe)"; echo "ixes $(sha256sum mathlib-78.ixes)"
  echo "ix git $(git -C "$HOME/repos/ix" rev-parse --short HEAD) $(git -C "$HOME/repos/ix" status --porcelain | grep -vc '^??') dirty files"
  echo "multi-stark pin $(grep -o 'multi-stark.git", rev = "[0-9a-f]*' "$HOME/repos/ix/Cargo.toml" | grep -o '[0-9a-f]*$' | cut -c1-7)"
  echo "driver $(nvidia-smi --query-gpu=driver_version --format=csv,noheader | head -1)"
  echo "thp $(cat /sys/kernel/mm/transparent_hugepage/enabled) / $(cat /sys/kernel/mm/transparent_hugepage/defrag)"
  echo "cpus $(nproc)  mem $(free -g | awk 'NR==2{print $2}') GiB"
  echo "flags --lanes 4 --exec-jobs $EXEC_JOBS --max-ram 230 $*  cap 920G"
  env | grep '^AIUR_\|^MULTI_STARK_' | sort
} > "$OUT/meta.txt"
nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu --format=csv,noheader,nounits --loop-ms=1000 > "$OUT/gpu.csv" 2>/dev/null &
SMI=$!
systemd-run --user --scope -q -p MemoryMax=920G -- \
  /usr/bin/time -v "$BIN" prove --ixe mathlib.ixe --ixes mathlib-78.ixes \
    --trace-shards --lanes 4 --exec-jobs $EXEC_JOBS --max-ram 230 "$@" > "$OUT/lanes.out" 2> "$OUT/lanes.err"
STATUS=$?
kill $SMI 2>/dev/null
echo "exit $STATUS" >> "$OUT/meta.txt"; echo "ended $(date -u +%FT%TZ)" >> "$OUT/meta.txt"
echo "$LABEL status=$STATUS"
grep -E "Elapsed|Maximum resident" "$OUT/lanes.err" | sed 's/^\s*//'
tail -1 "$OUT/lanes.out"
