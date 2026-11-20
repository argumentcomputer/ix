#!/usr/bin/env bash
# certify.sh NAME STAGE : the combined certificate for the environment
# .truthmines/combined/env/NAME.{ixe,ixes}, one resumable stage at a time.
#
#   leaves     prove each shard's CheckEnv claim (IxVM key), one gated job per shard
#   aggregate  join the leaf proofs under the Aiur-child aggregator (ix_aggr with shapes 17/18)
#   export     lay the aggregate root out as files, against a claim rebuilt from the environment
#   join       join the environment root with the training run's Aiur root into one AiurRun claim
#   check      check the joined root against everything recomputed from pinned inputs
#   compress   compress the joined root to a PLONK certificate with the pinned compression
#              pipeline, under a manifest that names the joined root's key
#
# THEOREM and BINDING name the refinement theorem and the binding in the environment (defaults:
# `IxAICombined.train_of_deployed_blocks_enc` and `IxAICombined.blockRun`). Work files go to
# .truthmines/combined/cert/NAME. The join tools
# and the `ix` that proves (profile `cert` of ix/ixw) come from the fork ~/repos/forks/ix-cert,
# built by build_cert.sh; its IxVM artifact and its aggregation artifact are kept by digest in
# ix/artifacts.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ix="$(dirname "$here")"
project="$(dirname "$ix")"
name=$1; stage=$2
env="$project/.truthmines/combined/env/$name.ixe"
manifest="$project/.truthmines/combined/env/$name.ixes"
work="$project/.truthmines/combined/cert/$name"
# Machine-specific locations, each overridable: the scratch disk for regenerable build output and
# caches (SCRATCH), the fork's checkout (IX_CERT_CHECKOUT), the join tools built from it (TOOLS),
# and the system CUDA driver library the nix-built prover needs preloaded (CUDA_PRELOAD).
scratch="${SCRATCH:-/opt/dlami/nvme/ix-ai/combined}"
checkout="${IX_CERT_CHECKOUT:-/home/sam/repos/forks/ix-cert}"
tools="${TOOLS:-$scratch/target/release/examples}"
cuda_preload="${CUDA_PRELOAD:-/usr/lib/x86_64-linux-gnu/libcuda.so.1}"
theorem="${THEOREM:-IxAICombined.train_of_deployed_blocks_enc}"
binding="${BINDING:-IxAICombined.blockRun}"
# The fork's pinned programs (tools/formal-aiur.keys); their artifacts are in ix/artifacts.
pins="$checkout/tools/formal-aiur.keys"
ixvm_digest=$(awk '$1 == "ixvm" { print $2 }' "$pins")
ixvm="$ix/artifacts/ixvm-$ixvm_digest.ixa"
aggr_digest=$(awk '$1 == "aggregation" { print $2 }' "$pins")
aggr="$ix/artifacts/aggregate-$aggr_digest.ixa"
block="$project/.truthmines/aiur/aiurexec-block"
run_root="$project/.truthmines/combined/run-root"
spec="$project/.truthmines/combined/spec"
store="${IXAI_HOME:-$project/.truthmines}/.ix/store"
cap="${STEP_CAP:-2400}"
# MAX_RAM is the prover's whole budget in GiB and MEM_CAP the scope's hard limit above it. The
# defaults leave room for other jobs on the machine; a run that has the machine to itself
# should raise both (the prover's own default is MemTotal less 20%).
ram="${MAX_RAM:-170}"
mem_cap="${MEM_CAP:-180}"
mkdir -p "$work"
export IX_PROFILE=cert
# The prover cuts a leaf whose execution record passes its ceiling into parts; the partition it
# proved is what the root's statement is built from.
proven="$work/proven.ixes"
rooted() { if [ -f "$proven" ]; then echo "$proven"; else echo "$manifest"; fi; }
log() { echo "$(date +%T) $*" | tee -a "$work/certify.log"; }
# One gated, timed, memory-capped job; its output goes to $work/$1.log.
job() {
  local tag=$1; shift
  "$ix/heavy.sh" systemd-run --user --scope -q -p MemoryMax="${mem_cap}G" -p MemorySwapMax=0 -- \
    /usr/bin/time -v -o "$work/$tag.time" timeout "$cap" "$@" > "$work/$tag.log" 2>&1
}
elapsed() { grep Elapsed "$work/$1.time" | awk '{print $NF}'; }

case "$stage" in
  leaves)
    n=$("$ix/ixw" shard claims "$env" --ixes "$manifest" 2>/dev/null | grep -cE '^[0-9]+ ')
    touch "$work/leaves.done"
    for k in $(seq 0 $((n - 1))); do
      grep -qx "$k" "$work/leaves.done" && continue
      job "leaf$k" "$ix/ixw" prove --ixe "$env" --ixes "$manifest" --shard "$k" --gpu-device 0 --max-ram "$ram"
      proof=$(tail -1 "$work/leaf$k.log")
      [[ "$proof" =~ [0-9a-f]{64} ]] || { log "leaf $k FAILED: $proof"; exit 1; }
      echo "$k" >> "$work/leaves.done"
      log "leaf $k proved in $(elapsed "leaf$k"): ${proof##* }"
    done ;;
  aggregate)
    # One prover run over every claim: executions overlap with proving, which separate runs per
    # shard cannot do. PROVE_FLAGS adds flags such as --fresh (reuse no earlier proof) or --texray.
    # shellcheck disable=SC2086
    job aggregate "$ix/ixw" prove --ixe "$env" --ixes "$manifest" --aggregate \
      --aggr-artifact "$aggr" --aggr-artifact-digest "$aggr_digest" --gpu-device 0 --max-ram "$ram" \
      --out-ixes "$proven" ${PROVE_FLAGS:-}
    root=$(tail -1 "$work/aggregate.log")
    [[ "$root" =~ ^[0-9a-f]{64}$ ]] || { log "aggregation FAILED: $root"; exit 1; }
    echo "$root" > "$work/aggregate.root"
    log "aggregate root $root in $(elapsed aggregate)" ;;
  export)
    rm -rf "$work/expected" "$work/env-root"
    "$tools/export_root" expected "$env" "$(rooted)" "$work/expected" > "$work/expected.json" || exit 1
    "$tools/export_root" extract "$ixvm" "$ixvm_digest" "$aggr" "$aggr_digest" "$(cat "$work/aggregate.root")" \
      "$work/expected/ix-claim.bin" "$work/env-root" "$store" > "$work/env-root.json" || exit 1
    log "exported environment root: $(tr -d '\n' < "$work/env-root.json" | cut -c1-300)" ;;
  join)
    rm -rf "$work/join" "$work/root"
    # aiur_join links the CUDA prover library from its cargo build directory (the newest build
    # there), and that library needs the system CUDA driver preloaded.
    cuda_lib=$(ls -t "$tools"/../build/multi-stark-*/out/libmulti_stark_cuda.so 2>/dev/null | head -1)
    export LD_LIBRARY_PATH="$(dirname "$cuda_lib")${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    export LD_PRELOAD="$cuda_preload"
    job join "$tools/aiur_join" join "$ixvm" "$ixvm_digest" "$aggr" "$aggr_digest" "$env" "$(rooted)" \
      "$work/env-root" "$run_root" "$theorem" "$binding" "$work/join" || { log "join FAILED: $(tail -3 "$work/join.log")"; exit 1; }
    "$tools/aiur_join" root "$ixvm" "$ixvm_digest" "$aggr" "$aggr_digest" "$work/join" "$work/root" > "$work/root.log" 2>&1 || exit 1
    log "joined in $(elapsed join): $(tail -1 "$work/root.log")" ;;
  check)
    "$tools/aiur_join_check" "$ixvm" "$ixvm_digest" "$aggr" "$aggr_digest" "$env" "$(rooted)" "$work/root" \
      "$block/aiur-exec.ixa" "$block/packages/block-000.ixa" "$run_root" "$spec/args.txt" "$spec/output.txt" \
      30 20 "$theorem" "$binding" > "$work/check.log" 2>&1
    status=$?
    tail -3 "$work/check.log"
    log "check exit $status"
    exit $status ;;
  compress)
    key=$("$tools/b3" "$work/root/root-vk.bin" | cut -d' ' -f1)
    # The pipeline's cache for this root key is several GB and regenerable: scratch disk when
    # there is one.
    cache="$work/pipeline-cache"
    [ -d "$scratch" ] && cache="$scratch/pipeline-cache-$name"
    sed -e "s|TO_BE_SET|$key|" -e "s|\"cache\": \"[^\"]*\"|\"cache\": \"$cache\"|" \
      "$project/.truthmines/combined/l3-combined.json.in" > "$work/pipeline.json"
    T="$ix/toolchain"
    export LD_PRELOAD="$cuda_preload"
    export IX_KZG_SRS="$T/base/target/compress-wrap/params/bn254-ignition-main-197/srs.bin"
    export IX_PARAMS_DIR="$T/base/target/compress-wrap/params"
    export IX_KZG_CUDA_SRS_CACHE=1 IX_PROFILE=pinned
    rm -rf "$work/plonk"
    job compress "$ix/ixw" compress aiur-ladder-run --ladder "$work/pipeline.json" \
      --ladder-blake3 "$("$tools/b3" "$work/pipeline.json" | cut -d' ' -f1)" --root-dir "$work/root" --out "$work/plonk" \
      || { log "compression FAILED: $(tail -3 "$work/compress.log")"; exit 1; }
    log "PLONK certificate: $(stat -c %s "$work/plonk/plonk/proof.bin") bytes in $(elapsed compress); checks: $(tr -d '\n ' < "$work/plonk/checks.json")" ;;
  *) echo "unknown stage $stage" >&2; exit 2 ;;
esac
