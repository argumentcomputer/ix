# Shared definitions for the multi-GPU lanes (docs/aiur-multi-gpu-design.md §4).
# Source from a run directory after setting IX, IXE and IXES:
#   IX=~/repos/ix/.lake/build/bin/ix IXE=init.ixe IXES=init-mincut-4.ixes . lanelib.sh
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_TRACE_SHARD_MAX_CELLS=${AIUR_TRACE_SHARD_MAX_CELLS:-1500000000}
export IX=${IX:?set IX to the ix binary} IXE=${IXE:?set IXE} IXES=${IXES:?set IXES}
export CAP=${CAP:-230G} CAP_HIGH=${CAP_HIGH:-220G}
export STAGE2_FLAGS="--direct-joins --structural-above 0 --trace-shards"

# run CPUS ARGS...: one proving command under the cgroup cap, pinned to CPUS
# (every thread pool sizes itself from the affinity mask).
run() { local cpus=$1; shift
  systemd-run --user --scope -q -p MemoryMax="$CAP" -p MemoryHigh="$CAP_HIGH" -- \
    taskset -c "$cpus" /usr/bin/time -v "$@"; }

# subtree_shards SLOT: the shard ids under plan slot SLOT, as `ix prove --shards` takes them.
subtree_shards() {
  "$IX" aggregate --ixe "$IXE" --ixes "$IXES" $STAGE2_FLAGS --plan-only --subtree "$1" \
    | sed -n "s/^subtree $1 shards: //p"; }
