#!/bin/sh
# lane.sh G SLOT [CPUS]: lane G on GPU G proves the claims under plan slot
# SLOT (Stage 1), then joins that subtree (Stage 2). Run from the run
# directory with IX, IXE and IXES set; CPUS defaults to twelve whole cores
# (both hyperthreads of each: on this host CPU n and n+48 are siblings, so
# a lane takes 12G..12G+11 and 48+12G..48+12G+11) so no two lanes share a
# core. Logs: laneG-stage1.{log,err}, laneG-stage2.{log,err};
# laneG-proofs.txt holds the lane's claim-proof addresses for the final run.
set -eu
. "$(dirname "$0")/lanelib.sh"
g=$1; T=$2
CPUS=${3:-"$((g*12))-$((g*12+11)),$((48+g*12))-$((48+g*12+11))"}
EXEC_JOBS=${EXEC_JOBS:-4}
export CUDA_VISIBLE_DEVICES=$g MULTI_STARK_CUDA_DEVICE=0

IDS=$(subtree_shards "$T")
[ -n "$IDS" ] || { echo "lane $g: no shards under slot $T" >&2; exit 1; }
echo "lane $g: GPU $g, CPUs $CPUS, subtree $T, shards $IDS"

run "$CPUS" "$IX" prove --ixe "$IXE" --ixes "$IXES" --trace-shards --retention regenerate \
  --max-ram 200 --exec-jobs "$EXEC_JOBS" --skip-proven --shards "$IDS" \
  > "lane$g-stage1.log" 2> "lane$g-stage1.err"
grep -E '^[0-9a-f]{64}$' "lane$g-stage1.log" > "lane$g-proofs.txt"
echo "lane $g: stage 1 done, $(wc -l < "lane$g-proofs.txt") proofs"

# shellcheck disable=SC2046
run "$CPUS" "$IX" aggregate --ixe "$IXE" --ixes "$IXES" $STAGE2_FLAGS \
  --jobs 1 --max-ram 200 --subtree "$T" $(cat "lane$g-proofs.txt") \
  > "lane$g-stage2.log" 2> "lane$g-stage2.err"
grep "subtree $T root:" "lane$g-stage2.err"
