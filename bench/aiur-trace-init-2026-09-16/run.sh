#!/usr/bin/env bash
# usage: run.sh <binary> <label> <mode: cpu|generated> <ixes> [lanes-args...]
set -u
S=/tmp/claude-30033/-home-sam-repos-ix/9c1af3d4-3a5f-4585-a0ae-b691c8d73308/scratchpad/bench
BIN=$1; LABEL=$2; MODE=$3; IXES=$4; shift 4
OUT=$S/runs/$LABEL; mkdir -p $OUT
export LD_LIBRARY_PATH=/nix/store/xm08aqdd7pxcdhm0ak6aqb1v7hw5q6ri-gcc-14.3.0-lib/lib:${LD_LIBRARY_PATH:-}
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000
export AIUR_GPU_TRACE=$MODE AIUR_LANES_CACHE_DIR=$OUT/cache AIUR_PROFILE=$OUT/spans.jsonl
export RUST_LOG=aiur::gpu_trace=debug,aiur::trace_codegen=debug
rm -rf $OUT/cache; mkdir -p $OUT/cache
nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader,nounits --loop-ms=1000 > $OUT/gpu.csv 2>/dev/null &
SMI=$!
/usr/bin/time -v $BIN prove --ixe $S/init.ixe --ixes $IXES --trace-shards --lanes 1 "$@" > $OUT/stdout.log 2> $OUT/stderr.log
STATUS=$?
kill $SMI 2>/dev/null
echo "$LABEL mode=$MODE status=$STATUS"
grep -E "Elapsed|Maximum resident|User time|System time" $OUT/stderr.log | sed 's/^\s*//'
grep -iE "root|verified|verdict|proof" $OUT/stdout.log | tail -4
grep -c "prepared generated CUDA trace" $OUT/stderr.log
grep -c "CPU trace: generated seed preparation failed" $OUT/stderr.log
