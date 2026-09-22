#!/bin/bash
# End-to-end env-shard baseline at 400 GiB on the current code: Stage 1 proves
# the nine measured env shards, Stage 2 aggregates them (wrap-first, scheduler
# gated to the same 400 GiB / --jobs 4 the trace range tree used), then the
# root is verified. Waits for the trace Stage 2 unit to finish first.
set -u
export PATH=/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin:$PATH
cd /home/ubuntu/ix-work
B=/home/ubuntu/ix/bench-2026-09-09; L=$B/logs
IXE=/home/ubuntu/ix/init-ts.ixe; IXES=$B/init-env400-measured.ixes
while systemctl --user is-active --quiet ix-stage2-range; do sleep 30; done
rev=$(git rev-parse --short HEAD)
echo "=== env400-e2e start $(date -u +%T) rev=$rev dirty=$(git status --porcelain | grep -vc '^??') inputs: $(sha256sum $IXE | cut -c1-16) $(sha256sum $IXES | cut -c1-16)"
lake build ix > $L/env400-e2e-build.log 2>&1 || { echo "build failed (rc=$?)"; exit 1; }
s1=env400-stage1-$rev
echo "=== $s1 start $(date -u +%T)"
timeout 60m /usr/bin/time -v lake exe ix prove --ixe $IXE --ixes $IXES --max-ram 400 --texray --no-index > $L/$s1.log 2>&1
rc=$?
echo "rc=$rc $s1 $(date -u +%T) $(grep -E 'Elapsed \(wall' $L/$s1.log | sed 's/.*: //') maxrss_kb=$(grep -E 'Maximum resident' $L/$s1.log | grep -oE '[0-9]+$') proofs=$(grep -cE '^[0-9a-f]{64}$' $L/$s1.log)"
[ $rc -eq 0 ] || { echo "stage 1 failed"; exit 1; }
addrs=$(grep -E '^[0-9a-f]{64}$' $L/$s1.log | tr '\n' ' ')
s2=env400-stage2-j4-$rev
echo "=== $s2 start $(date -u +%T)"
timeout 90m /usr/bin/time -v lake exe ix aggregate --ixe $IXE --ixes $IXES --no-cache --jobs 4 --max-ram 400 $addrs > $L/$s2.log 2>&1
rc=$?
echo "rc=$rc $s2 $(date -u +%T) $(grep -E 'Elapsed \(wall' $L/$s2.log | sed 's/.*: //') maxrss_kb=$(grep -E 'Maximum resident' $L/$s2.log | grep -oE '[0-9]+$')"
grep -E '\[aggregate\] (plan|scheduler|slot .* proven|root proof)|error' $L/$s2.log | cut -c1-200
[ $rc -eq 0 ] || { echo "stage 2 failed"; exit 1; }
root=$(grep -oE 'root proof: [0-9a-f]{64}' $L/$s2.log | tail -1 | cut -d' ' -f3)
timeout 10m lake exe ix verify --aggregate --ixe $IXE --ixes $IXES $root > $L/$s2-verify.log 2>&1
echo "rc=$? verify: $(grep -E '^ok|FAIL|error|\[verify\]' $L/$s2-verify.log | head -4 | cut -c1-200)"
