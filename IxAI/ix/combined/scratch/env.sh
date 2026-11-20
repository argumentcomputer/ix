#!/usr/bin/env bash
# env.sh STAGE: the combined environment through ix (ix.ci-merge-tests via ixw, profile ci), each
# stage timed and capped at 180G; prove is resumable and capped at 2700 s per invocation.
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
E=$P/.truthmines/combined/env
SRC=$P/.truthmines/combined/src/Aiur
mkdir -p $E
cap() { systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $E/$1.time "${@:2}"; }
export IX_PROFILE=ci
case "$1" in
  compile) cd $SRC && PATH=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1/bin:$PATH cap lake timeout 2700 lake build IxAICombined > $E/lake.log 2>&1 \
      || { tail -40 $E/lake.log; exit 1; }
    cap compile timeout 2700 $P/ix/ixw compile IxAICombined.lean --local --no-build \
      --out $E/combined.ixe --report $E/compile.json > $E/compile.log 2>&1 ;;
  check) cap check timeout 2700 $P/ix/ixw check-lean $E/combined.ixe > $E/check.log 2>&1 ;;
  shard) cap shard timeout 1200 $P/ix/ixw shard $E/combined.ixe --max-ram 170 --out $E/combined.ixes > $E/shard.log 2>&1 ;;
  prove)
    export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$E/cache
    nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu --format=csv,noheader,nounits --loop-ms=2000 >> $E/prove.gpu.csv 2>/dev/null &
    smi=$!
    cap prove.$(date +%s) timeout 2700 $P/ix/ixw prove --ixe $E/combined.ixe --ixes $E/combined.ixes --aggregate \
      --out-ixes $E/proven.ixes --max-ram 170 --gpu-device 0 >> $E/prove.out 2>> $E/prove.err
    st=$?; kill $smi; exit $st ;;
  *) echo "unknown stage $1"; exit 2 ;;
esac
st=$?; tail -5 $E/$1.log; exit $st
