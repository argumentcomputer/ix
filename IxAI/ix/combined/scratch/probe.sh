#!/usr/bin/env bash
# probe.sh: certified compile of single constants' closures, timed, to find what dominates.
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
N=/opt/dlami/nvme/ix-ai/combined/compile/probe
cd $P/.truthmines/combined/src/Aiur
export IX_PROFILE=ci
i=0
while IFS= read -r name; do
  i=$((i+1)); echo "$name" > $N/c$i.txt
  systemd-run --user --scope -q -p MemoryMax=120G -p MemorySwapMax=0 -- /usr/bin/time -v -o $N/c$i.time \
    timeout ${PROBE_CAP:-600} $P/ix/ixw compile IxAICombined.lean --consts-file $N/c$i.txt --no-build -v --workers 24 \
    --out $N/c$i.ixe > $N/c$i.log 2>&1
  st=$?
  printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$st" "$(grep -o 'after transitive-dep closure' -B0 $N/c$i.log | head -0; grep -oE '[0-9]+ constants after' $N/c$i.log | head -1)" \
    "$(grep -E 'Elapsed' $N/c$i.time | awk '{print $NF}')" "$(grep -E 'Maximum res' $N/c$i.time | awk '{print $NF}')" | tee -a $N/summary.tsv
  grep -E "\[compile\] (canon|compileReport)" $N/c$i.log
  rm -f $N/c$i.ixe
done <<'NAMES'
IxAICore.train
Aiur.Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed
IxAIStep.Fixed.Obs.«Fixed::shr8».obs
IxAIStep.Fixed.Obs.«Fixed::hidden».obs
IxAIStep.Fixed.Obs.«Fixed::transpose20x16».obs
NAMES
