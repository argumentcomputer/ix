#!/usr/bin/env bash
# dt-seeds.sh OUT ARGS… : seeds 1..8 of the differential tester in parallel, each capped at 8G and
# one hour; one log per seed in OUT/, then each seed's tallies to stdout. Run from anywhere after
# `lake -d ModeRepairTests build difftest` (MT's dt-seeds.sh, without the per-tree package).
# The 800,000-program run: dt-seeds.sh OUT --n 100000 --shrink 300 --classify --stuck 4
set -u
D=$(cd "$(dirname "$0")" && pwd)
OUT="$1"; shift
mkdir -p "$OUT"
date -u
for s in 1 2 3 4 5 6 7 8; do
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 timeout 3600 \
    "$D/.lake/build/bin/difftest" --seed $s --out "$OUT" "$@" > "$OUT/seed-$s.log" 2>&1 &
done
wait
date -u
for s in 1 2 3 4 5 6 7 8; do echo "=== seed $s"; sed -n "/^seed $s done/,\$p" "$OUT/seed-$s.log"; done
