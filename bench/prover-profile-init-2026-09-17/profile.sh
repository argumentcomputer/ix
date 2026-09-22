#!/usr/bin/env bash
# usage: profile.sh <binary> <label> <claim K | join N> [extra env assignments via environment]
set -u
S=${BENCH_SCRATCH:?set BENCH_SCRATCH to the directory holding init.ixe, init-4.ixes and runs/}
BIN=$1; LABEL=$2; KIND=$3; INDEX=$4; shift 4
OUT=$S/profiles/$LABEL; mkdir -p $OUT
export LD_LIBRARY_PATH=/nix/store/xm08aqdd7pxcdhm0ak6aqb1v7hw5q6ri-gcc-14.3.0-lib/lib:${LD_LIBRARY_PATH:-}
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export CUDA_VISIBLE_DEVICES=0 AIUR_GPU_TRACE=${AIUR_GPU_TRACE:-generated} AIUR_TRACE_ONLY_LOOKUPS=1
export AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000
export RAYON_NUM_THREADS=24 LEAN_NUM_THREADS=24
export AIUR_PROFILE=$OUT/spans.jsonl AIUR_CUDA_PROFILE=$OUT/cuda.jsonl
export CUDA_INJECTION64_PATH=/home/sam/repos/ix/target/prover-profile-build/libcupti_trace.so
export AIUR_AGGREGATE_CACHE_DIR=$S/runs/q4-cache2-generated/cache/aggregate
export AIUR_LANES_CACHE_DIR=$S/runs/q4-cache2-generated/cache
rm -f $OUT/spans.jsonl $OUT/cuda.jsonl
if [ "$KIND" = claim ]; then
  CMD="$BIN prove --ixe $S/init.ixe --ixes $S/init-4.ixes --trace-shards --max-ram 200 --shard $INDEX --no-index --texray"
else
  CMD="$BIN aggregate --ixe $S/init.ixe --ixes $S/init-4.ixes --trace-shards --max-ram 200 --direct-joins --jobs 1 --no-write --reprove-slot $INDEX"
fi
echo "$CMD" > $OUT/command
nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu,power.draw --format=csv,noheader,nounits --loop-ms=200 > $OUT/gpu.csv 2>/dev/null &
SMI=$!
/usr/bin/time -v taskset -c 8-31 $CMD "$@" > $OUT/stdout 2> $OUT/stderr
STATUS=$?
kill $SMI 2>/dev/null
echo "$LABEL $KIND $INDEX status=$STATUS"
grep -E "Elapsed|Maximum resident|User time" $OUT/stderr | sed 's/^\s*//'
wc -l $OUT/cuda.jsonl $OUT/spans.jsonl 2>/dev/null
