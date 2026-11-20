#!/usr/bin/env bash
# exec_leaves.sh ENV.ixe ENV.ixes OUT_DIR JOBS MEM_GIB LEAF... : execute (no proof) the named
# leaves of a partition in IxVM, JOBS at a time, each in its own scope capped at MEM_GIB with ix
# planning 10 GiB below that. Writes OUT_DIR/leafK.{log,time} and one line per leaf to
# OUT_DIR/status: leaf, exit status, wall time, peak RSS (kB), queries.
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
env=$1; manifest=$2; out=$3; jobs=$4; mem=$5; shift 5
mkdir -p "$out"
export IX_PROFILE="${IX_PROFILE:-ci-pinned}"
one() {
  local k=$1
  systemd-run --user --scope -q -p MemoryMax="${mem}G" -p MemorySwapMax=0 -- \
    /usr/bin/time -v -o "$out/leaf$k.time" timeout "${STEP_CAP:-1500}" \
    $P/ix/ixw prove --ixe "$env" --ixes "$manifest" --shard "$k" --exec-only --max-ram "$((mem - 10))" \
    > "$out/leaf$k.log" 2>&1
  local st=$?
  printf '%s\t%s\t%s\t%s\t%s\n' "$k" "$st" \
    "$(grep Elapsed "$out/leaf$k.time" 2>/dev/null | awk '{print $NF}')" \
    "$(grep 'Maximum res' "$out/leaf$k.time" 2>/dev/null | awk '{print $NF}')" \
    "$(grep -oE '"queries":[0-9]+' "$out/leaf$k.log" | head -1 | cut -d: -f2)" >> "$out/status"
}
export -f one
export P env manifest out mem
printf '%s\n' "$@" | xargs -P "$jobs" -I{} bash -c 'one {}'
