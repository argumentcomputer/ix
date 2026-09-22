#!/bin/bash
# End-to-end Init on the fork with the Blake3 and LDE kernel work: Stage 1
# distributed (8 ordered chunks) then Stage 2 (derived range, lookahead),
# both verified, under the cap. Reference: ns-dist8 6:26 / v13 range28 3:46.
set -u
cd ~/benchdata/trace-shards-gpu; source ./runlib.sh
until grep -qE "^=== done" build-gpu2.log; do sleep 20; done
grep -q "^exit=0" build-gpu2.log || { echo "BUILD FAILED"; grep -n "error" -A4 build-gpu2.log | head -20; exit 1; }
export AIUR_TRACE_SHARD_MAX_CELLS=1500000000
run gpu2-dist8 ./ix-cuda-gpu2 prove --ixe init.ixe --ixes init-ordered-8.ixes --distributed --cells 1500000000 --max-ram 200 --texray --no-index
BATCH=$(grep -oE "^[0-9a-f]{64}$" init-gpu-gpu2-dist8.log | head -1)
[ -z "$BATCH" ] && { echo "no batch proof, stopping"; exit 1; }
tag=gpu2-stage2-range0
echo "=== $tag $(date)"
env AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 \
  systemd-run --user --scope -q -p MemoryMax=230G -p MemoryHigh=220G -- \
  /usr/bin/time -v ./ix-cuda-gpu2 aggregate --ixe init.ixe --ixes init-1.ixes --no-cache --jobs 1 --max-ram 100 --trace-shards --range 0 --texray $BATCH > init-gpu-$tag.log 2>&1 &
TPID=$!; sleep 3; PID=$(pgrep -f "^\./ix-cuda-gpu2 aggregate" | head -1); [ -z "$PID" ] && PID=$TPID
sampler $PID init-gpu-$tag-util.log & S=$!; watchdog $PID init-gpu-$tag.log; wait $TPID; wait $S
grep -E "Elapsed|Maximum resident|Exit status|panicked|WATCHDOG|range tree over|executed in|proven in|range tree total" init-gpu-$tag.log | sed -E 's/\[aggregate\] slot 0: //'
ROOT=$(grep -oE "root proof: [0-9a-f]{64}" init-gpu-$tag.log | tail -1 | cut -d" " -f3); echo "root $ROOT"
[ -n "$ROOT" ] && { ls -la ~/.ix/store/$(echo $ROOT | sed -E 's/^(..)(..)(..)(.*)$/\1\/\2\/\3\/\4/') | awk '{print "root bytes", $5}'; ./ix-cuda-gpu2 verify --aggregate --ixe init.ixe --ixes init-1.ixes $ROOT 2>&1 | tail -1; }
echo "=== queue22 done $(date)"
