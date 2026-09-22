#!/bin/bash
# Stage 1 of the distributed Init batch with commit-ordered execution and
# re-execution for round two: all four workers executing at once, then one
# at a time. Builds once (codegen check included) before any timed run,
# records the inputs' hashes, bounds every run, and verifies each proof.
set -u
export PATH=/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin:$PATH
cd /home/ubuntu/ix-work
B=/home/ubuntu/ix/bench-2026-09-09; L=$B/logs
IXE=/home/ubuntu/ix/init-ts.ixe; IXES=$B/init-4.ixes
echo "=== build $(date -u +%T) rev=$(git rev-parse --short HEAD) dirty=$(git status --porcelain | grep -vc '^??') multi-stark=$(git -C /home/ubuntu/multi-stark rev-parse --short HEAD)"
lake exe ix codegen --check > $L/regen-build.log 2>&1 || { echo "codegen check failed (rc=$?)"; exit 1; }
echo "inputs: $(sha256sum $IXE | cut -c1-16) $(sha256sum $IXES | cut -c1-16)"
for jobs in ${JOBS_LIST:-4 1}; do
  name=dist4-vram-regen-prefetch-j$jobs
  echo "=== $name start $(date -u +%T)"
  timeout 90m /usr/bin/time -v lake exe ix prove --ixe $IXE --ixes $IXES --distributed --cells 1800000000 --exec-jobs $jobs --texray --no-index > $L/$name.log 2>&1
  rc=$?
  echo "rc=$rc $name $(date -u +%T) $(grep -E 'Elapsed \(wall' $L/$name.log | sed 's/.*: //') maxrss_kb=$(grep -E 'Maximum resident' $L/$name.log | grep -oE '[0-9]+$')"
  grep -E '^\[distributed\]|^claim |^[0-9a-f]{64}$|error' $L/$name.log | head -30 | cut -c1-220
  [ $rc -eq 0 ] || { echo "run failed"; exit 1; }
  addr=$(grep -E '^[0-9a-f]{64}$' $L/$name.log | tail -1)
  timeout 10m lake exe ix verify --ixe $IXE --ixes $B/init-1.ixes $addr > $L/$name-verify.log 2>&1
  echo "rc=$? verify $name: $(grep -E '^ok|FAIL|error' $L/$name-verify.log | head -2 | cut -c1-160)"
done
