#!/bin/bash
# Record residency with the dependency-ordered layout: exec-only over the
# 8-leaf ordered manifest for record sizes, then Stage 1 of all Init as one
# claim at the 1.8 G cell budget for the peak. Waits for the env-400 chain.
set -u
export PATH=/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin:$PATH
cd /home/ubuntu/ix-lab
B=/home/ubuntu/ix/bench-2026-09-09; L=$B/logs
IXE=/home/ubuntu/ix/init-ts.ixe; IXES=$B/init-ordered-8.ixes
while systemctl --user is-active --quiet ix-env400-e2e; do sleep 30; done
rev=$(git rev-parse --short HEAD)
echo "=== ordered start $(date -u +%T) rev=$rev dirty=$(git status --porcelain | grep -vc '^??') inputs: $(sha256sum $IXE | cut -c1-16) $(sha256sum $IXES | cut -c1-16)"
lake build ix > $L/ordered-build.log 2>&1 || { echo "build failed (rc=$?)"; exit 1; }
name=ordered8-exec-$rev
timeout 30m /usr/bin/time -v lake exe ix prove --ixe $IXE --ixes $IXES --distributed --exec-only --no-index > $L/$name.log 2>&1
echo "rc=$? $name $(date -u +%T) $(grep -E 'Elapsed \(wall' $L/$name.log | sed 's/.*: //') maxrss_kb=$(grep -E 'Maximum resident' $L/$name.log | grep -oE '[0-9]+$')"
grep -E '^\[distributed\]' $L/$name.log | cut -c1-200
name=ordered8-vram-regen-$rev
timeout 90m /usr/bin/time -v lake exe ix prove --ixe $IXE --ixes $IXES --distributed --cells 1800000000 --texray --no-index > $L/$name.log 2>&1
rc=$?
echo "rc=$rc $name $(date -u +%T) $(grep -E 'Elapsed \(wall' $L/$name.log | sed 's/.*: //') maxrss_kb=$(grep -E 'Maximum resident' $L/$name.log | grep -oE '[0-9]+$')"
grep -E '^\[distributed\]|^claim |^[0-9a-f]{64}$|error' $L/$name.log | head -40 | cut -c1-200
[ $rc -eq 0 ] || { echo "run failed"; exit 1; }
addr=$(grep -E '^[0-9a-f]{64}$' $L/$name.log | tail -1)
timeout 10m lake exe ix verify --ixe $IXE --ixes $B/init-1.ixes $addr > $L/$name-verify.log 2>&1
echo "rc=$? verify $name: $(grep -E '^ok|FAIL|error' $L/$name-verify.log | head -2 | cut -c1-160)"
