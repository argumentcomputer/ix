#!/usr/bin/env bash
# Mergesort prove at shard-bytes 250 kB with --max-witness-stored 10
# (overrides the project default of 5 — validates the post-Blake3f RAM
# model). Runs in the foreground; full log streams to terminal and is
# also captured at zisk/logs/mergesort-250k.log.
#
# Predicted RAM model with Blake3f precompile + mws=10:
#   peak ≈ 40 GB stream overhead + 10 × 16 GB per witness  ≈ ~200 GB
#
# Per-shard wall (mws=10 has full parallelism vs mws=5's ~85 %):
#   ~310 s per shard, ~25-30 min total over ~5 shards.
#
# Monitor RAM/swap/GPU live in side terminals:
#   watch -n 2 'free -h && echo && grep -E "^(si|so)" /proc/vmstat'
#   nvidia-smi --query-gpu=memory.used,memory.free,utilization.gpu --format=csv -l 5
#
# Kill cleanly with Ctrl-C.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ZISK_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
LOG_DIR="$ZISK_DIR/logs"
mkdir -p "$LOG_DIR"
LOG="$LOG_DIR/mergesort-250k.log"

cd "$ZISK_DIR"

# Pin the CUDA JIT compile cache to its 4 GB hard max so proving kernels
# stay cached across shards/runs instead of being LRU-evicted and re-JIT'd
# (default cap is ~1 GB; see scripts/prove-batch.sh and the README).
export CUDA_CACHE_MAXSIZE="${CUDA_CACHE_MAXSIZE:-4294967296}"

# Memory watchdog: SIGKILLs the prover if used RAM exceeds MEM_LIMIT_GIB
# (default 200 GiB). This run uses --max-witness-stored 10 (~200 GB peak),
# so the guard is the safety net against an OOM on the 256 GB box.
source "$SCRIPT_DIR/mem-guard.sh"

echo "[$(date '+%H:%M:%S')] start  mergesort --shard-bytes 250000 --max-witness-stored 10" | tee "$LOG"

run_guarded cargo run --release --bin zisk-host --quiet -- \
  --gpu \
  --shard-bytes 250000 \
  --max-witness-stored 10 \
  --ixe /home/ubuntu/ix/mergesort.ixe \
  2>&1 | tee -a "$LOG"

echo "[$(date '+%H:%M:%S')] done   mergesort --shard-bytes 250000 --max-witness-stored 10" | tee -a "$LOG"
