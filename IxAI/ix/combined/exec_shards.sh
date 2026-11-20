#!/usr/bin/env bash
# exec_shards.sh ENV.ixe ENV.ixes N OUT_DIR : execute (no proof) each of the N shards of an
# environment in IxVM, timed and memory-capped, to validate the kernel check and size the proof.
# ix plans against MAX_RAM GiB (default 170), which must stay below the scope's 180G limit: left
# to its own default (MemTotal less 20%) it grows a record past the limit and is killed.
# Writes OUT_DIR/shardK.{log,time}, OUT_DIR/status and OUT_DIR/done.
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
env=$1; manifest=$2; n=$3; out=$4
mkdir -p "$out"; rm -f "$out/done" "$out/status"
export IX_PROFILE="${IX_PROFILE:-ci-pinned}"
for k in $(seq 0 $((n - 1))); do
  systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- \
    /usr/bin/time -v -o "$out/shard$k.time" timeout "${STEP_CAP:-2400}" \
    $P/ix/ixw prove --ixe "$env" --ixes "$manifest" --shard "$k" --exec-only --max-ram "${MAX_RAM:-170}" > "$out/shard$k.log" 2>&1
  echo "shard $k exit $?" >> "$out/status"
done
echo ok > "$out/done"
