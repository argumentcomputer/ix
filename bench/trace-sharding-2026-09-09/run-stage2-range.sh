#!/bin/bash
# Stage 2 of a distributed Init batch as a range-sum tree, then verify the
# root. SRC names the Stage 1 log whose last printed address is the batch
# proof; the log name carries the source run and the ix commit.
set -u
export PATH=/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin:$PATH
cd /home/ubuntu/ix-work
B=/home/ubuntu/ix/bench-2026-09-09; L=$B/logs
IXE=/home/ubuntu/ix/init-ts.ixe; IXES=$B/init-1.ixes
SRC=${SRC:-dist4-vram-regen-prefetch-j4}; RANGE=${RANGE:-12}; JOBS=${JOBS:-4}; RAM=${RAM:-400}
name=stage2-${SRC}-range$RANGE-j$JOBS-$(git rev-parse --short HEAD)
addr=$(grep -E "^[0-9a-f]{64}$" $L/$SRC.log | tail -1)
echo "=== $name start $(date -u +%T) rev=$(git rev-parse --short HEAD) dirty=$(git status --porcelain | grep -vc '^??') batch=$addr"
lake build ix > $L/$name-build.log 2>&1 || { echo "build failed (rc=$?)"; exit 1; }
timeout 90m /usr/bin/time -v lake exe ix aggregate --ixe $IXE --ixes $IXES --no-cache --jobs $JOBS --max-ram $RAM --trace-shards --range $RANGE $addr > $L/$name.log 2>&1
rc=$?
echo "rc=$rc $name $(date -u +%T) $(grep -E 'Elapsed \(wall' $L/$name.log | sed 's/.*: //') maxrss_kb=$(grep -E 'Maximum resident' $L/$name.log | grep -oE '[0-9]+$')"
grep -E '\[aggregate\]|error' $L/$name.log | cut -c1-200
[ $rc -eq 0 ] || { echo "run failed"; exit 1; }
root=$(grep -oE 'root proof: [0-9a-f]{64}' $L/$name.log | tail -1 | cut -d' ' -f3)
timeout 10m lake exe ix verify --aggregate --ixe $IXE --ixes $IXES $root > $L/$name-verify.log 2>&1
echo "rc=$? verify: $(grep -E '^ok|FAIL|error|\[verify\]' $L/$name-verify.log | head -4 | cut -c1-200)"
