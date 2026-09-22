#!/bin/bash
# Static residency analysis, no execution: for each manifest, the
# distributed prover's caller groups and commit order (plan-only). Also cuts
# dependency-ordered manifests of Init at 4, 8 and 16 leaves to compare with
# the min-cut ones. Pinned to eight cores; a benchmark may be running.
set -u
export PATH=/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin:$PATH
cd /home/ubuntu/ix-lab
B=/home/ubuntu/ix/bench-2026-09-09; L=$B/logs
IXE=/home/ubuntu/ix/init-ts.ixe
echo "=== plan start $(date -u +%T) rev=$(git rev-parse --short HEAD) dirty=$(git status --porcelain | grep -vc '^??')"
for n in 4 8 16; do
  taskset -c 56-63 lake exe ix shard $IXE --shards $n --ordered --out $B/init-ordered-$n.ixes > $L/shard-ordered-$n.log 2>&1
  echo "rc=$? shard ordered $n: $(grep -E 'backward edges|spread' $L/shard-ordered-$n.log | tail -1 | cut -c1-160)"
done
for m in init-4 init-8 init-16 init-ordered-4 init-ordered-8 init-ordered-16; do
  taskset -c 56-63 lake exe ix prove --ixe $IXE --ixes $B/$m.ixes --distributed --plan-only --no-index > $L/plan-$m.log 2>&1
  echo "rc=$? plan $m: $(grep -E 'plan: [0-9]+ groups' $L/plan-$m.log | cut -c1-200)"
  grep -E 'plan: worker' $L/plan-$m.log | cut -c1-160
done
