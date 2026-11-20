#!/usr/bin/env bash
# Certify a large environment end to end, politely and resumably:
#   1. prove each shard of ENV.ixes as its own gated job (heavy.sh takes and releases the
#      shared heavy-job lock per shard, so other sessions can interleave);
#   2. aggregate the cached leaf proofs into one root;
#   3. export the raw root and compress it to PLONK with the pinned ladder;
#   4. record every step in .truthmines/index.tsv.
# Finished shards are listed in STATE and skipped on a rerun.
#   SHARDS=N certify-full.sh ENV.ixe ENV.ixes LABEL
# Each prove, check or compression run is capped at STEP_CAP seconds (default 1800) after the
# gate grants the machine; waiting for the gate does not count.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
project="$(dirname "$here")"
env="$1"; manifest="$2"; label="$3"
state="$project/.truthmines/compression/$label.shards.done"
index="$project/.truthmines/index.tsv"
out="$project/.truthmines/compression"
export IX_PROFILE=ci-pinned
aggr="$here/artifacts/stark-export-7d687ca0a7815bb5c4a68b94276fe797bb3a9f909b2da795267ac8ec9184c4d1.ixa"
aggr_digest=7d687ca0a7815bb5c4a68b94276fe797bb3a9f909b2da795267ac8ec9184c4d1
ixvm="$here/artifacts/ixvm-5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576.ixa"
ixvm_digest=5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576
touch "$state"
n=${SHARDS:?set SHARDS to the number of shards in the manifest}
log() { echo "$(date +%T) $*" | tee -a "$out/$label.log"; }
log "certifying $env with $n shards"
for k in $(seq 0 $((n - 1))); do
  if grep -qx "$k" "$state"; then continue; fi
  start=$(date +%s)
  result=$("$here/heavy.sh" timeout "${STEP_CAP:-1800}" "$here/ixw" prove --ixe "$env" --ixes "$manifest" --shard "$k" --gpu-device 0 2>&1 | tail -1)
  secs=$(( $(date +%s) - start ))
  if [[ "$result" =~ [0-9a-f]{64} ]]; then
    echo "$k" >> "$state"
    log "shard $k proved in ${secs}s: $result"
    printf 'shard\t%s.shard%s\t-\t-\t-\t%s\t%s\t-\tverified\n' "$label" "$k" "${result##* }" "$secs" >> "$index"
  else
    log "shard $k FAILED after ${secs}s: $result"
    exit 1
  fi
done
log "aggregating"
start=$(date +%s)
root=$("$here/heavy.sh" timeout "${STEP_CAP:-1800}" "$here/ixw" prove --ixe "$env" --ixes "$manifest" --aggregate \
  --aggr-artifact "$aggr" --aggr-artifact-digest "$aggr_digest" --gpu-device 0 2>&1 | tail -1)
[[ "$root" =~ ^[0-9a-f]{64}$ ]] || { log "aggregation FAILED: $root"; exit 1; }
log "aggregate root $root in $(( $(date +%s) - start ))s"
"$here/toolchain/bin/export_root" expected "$env" "$manifest" "$out/$label.expected" > "$out/$label.expected.json"
"$here/toolchain/bin/export_root" extract "$ixvm" "$ixvm_digest" "$aggr" "$aggr_digest" "$root" \
  "$out/$label.expected/ix-claim.bin" "$out/$label.root" "$project/.truthmines/.ix/store" > "$out/$label.root.json"
log "exported root: $(python3 -c "import json;d=json.load(open('$out/$label.root.json'));print(d['key_blake3'],d['verified'],d['proof_bytes'])")"
start=$(date +%s)
"$here/ladder.sh" "$out/$label.root" "$out/$label.ladder" > "$out/$label.ladder.log" 2>&1 || { log "ladder FAILED"; exit 1; }
secs=$(( $(date +%s) - start ))
bytes=$(stat -c %s "$out/$label.ladder/plonk/proof.bin")
claim=$(python3 -c "import json;print(json.load(open('$out/$label.root.json'))['ix_claim_blake3'])")
printf 'compress\t%s.(environment)\t%s\t-\t%s\tplonk:%s\t%s\t%s\tverified\n' "$label" "$root" "$claim" \
  "${out#$project/}/$label.ladder/plonk/proof.bin" "$secs" "$bytes" >> "$index"
log "PLONK certificate: $bytes bytes in ${secs}s; checks: $(cat "$out/$label.ladder/checks.json" | tr -d '\n ')"
