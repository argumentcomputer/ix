#!/usr/bin/env bash
# timed_run.sh NAME : the whole certificate for the environment
# .truthmines/combined/env/NAME.{ixe,ixes}, end to end under one clock, reusing no proof:
#
#   train     the training run's root: block proofs, their tree and wraps (train_run.sh)
#   env       the environment's leaf proofs and aggregation in one prover run (certify.sh aggregate)
#   export    the environment root laid out as files
#   join      the environment root joined with the training root into one AiurRun claim
#   check     the independent check of the joined root (aiur_join_check)
#   compress  the joined root compressed to a PLONK certificate
#
# The clock covers everything a prover does from compiled inputs: it starts before the first
# proof and stops when the certificate is written. Proving keys, fixed preprocessing and the
# compression pipeline's parameters are reused; proofs are not (`--fresh`, emptied work
# directories, an empty compression cache). The independent check runs inside the clock because
# nothing is compressed before it passes.
#
# Run as one gated job, so that nothing else starts between stages:
#   HEAVY_PRIORITY=2 ix/heavy.sh ix/combined/timed_run.sh NAME
# While it runs, .truthmines/QUIET keeps the light lane out. Results: cert/NAME/timeline.tsv
# (stage, seconds, cumulative), cert/NAME/timed.log, and the stage logs of certify.sh and
# train_run.sh under cert/NAME and cert/NAME/train.
#
# Settings: MAX_RAM (default 200) and MEM_CAP (default 230) for a machine the run has to itself;
# CHECK_FLAGS, further options for aiur_join_check. For the environment's prover run only:
# ENV_GPU_TRACE (default cpu) and ENV_SHARD_CELLS (default 2100000000). With these heavy claims
# the device record of all eligible circuits does not fit beside the trace shards, so the
# planner populates almost everything on the host whatever the mode; without a device record
# the card holds larger shards, and fewer shards mean fewer host supplies. The other stages keep
# their own defaults.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ix="$(dirname "$here")"
project="$(dirname "$ix")"
name=$1
work="$project/.truthmines/combined/cert/$name"
scratch="${SCRATCH:-/opt/dlami/nvme/ix-ai/combined}"
quiet="$project/.truthmines/QUIET"

[ -n "${HEAVY_HELD:-}" ] || { echo "timed_run.sh: run it through ix/heavy.sh, as one job" >&2; exit 2; }
for f in "$project/.truthmines/combined/env/$name.ixe" "$project/.truthmines/combined/env/$name.ixes"; do
  [ -f "$f" ] || { echo "timed_run.sh: missing $f" >&2; exit 2; }
done

export MAX_RAM="${MAX_RAM:-200}" MEM_CAP="${MEM_CAP:-230}"
env_trace="${ENV_GPU_TRACE:-cpu}"
env_cells="${ENV_SHARD_CELLS:-2100000000}"
unset AIUR_GPU_TRACE AIUR_TRACE_SHARD_MAX_CELLS
export STEP_CAP="${STEP_CAP:-7200}"
export RUN_ROOT="$work/train/run-root"

rm -rf "$work" "$scratch/pipeline-cache-$name"
mkdir -p "$work"
: > "$quiet"
trap 'rm -f "$quiet"' EXIT
timeline="$work/timeline.tsv"
: > "$timeline"
{
  echo "started $(date -u +%FT%TZ) on $(hostname)"
  echo "environment $(python3 -c "import json; d = json.load(open('$project/.truthmines/combined/env/$name.json')); print(d.get('root'), d.get('requested'), 'constants')" 2>/dev/null)"
  echo "pins $(grep -E '^(ixvm|aggregation) ' "${IX_CERT_CHECKOUT:-/home/sam/repos/forks/ix-cert}/tools/formal-aiur.keys" | tr '\n' ' ')"
  echo "settings MAX_RAM=$MAX_RAM MEM_CAP=$MEM_CAP; environment run AIUR_GPU_TRACE=$env_trace AIUR_TRACE_SHARD_MAX_CELLS=$env_cells"
  echo "load $(cut -d' ' -f1-3 /proc/loadavg); other busy processes: $(ps -eo pcpu,comm --sort=-pcpu | awk 'NR>1 && $1>50 {printf "%s(%s%%) ", $2, $1}')"
} > "$work/timed.log"

t0=$(date +%s.%N)
last=$t0
stage() {
  local label=$1; shift
  "$@" >> "$work/timed.log" 2>&1
  local st=$? now; now=$(date +%s.%N)
  printf '%s\t%.1f\t%.1f\n' "$label" "$(echo "$now - $last" | bc)" "$(echo "$now - $t0" | bc)" >> "$timeline"
  last=$now
  if [ $st -ne 0 ]; then
    echo "timed_run.sh: stage $label failed ($st); see $work/timed.log" >&2
    printf 'FAILED\t%s\t%s\n' "$label" "$st" >> "$timeline"
    exit $st
  fi
}

stage train    "$here/train_run.sh" "$work/train" roots tree wraps
stage env      env PROVE_FLAGS="--fresh" AIUR_GPU_TRACE="$env_trace" AIUR_TRACE_SHARD_MAX_CELLS="$env_cells" \
               "$here/certify.sh" "$name" aggregate
stage export   "$here/certify.sh" "$name" export
stage join     "$here/certify.sh" "$name" join
# shellcheck disable=SC2086
stage check    env CHECK_FLAGS="${CHECK_FLAGS:-}" "$here/certify.sh" "$name" check
stage compress "$here/certify.sh" "$name" compress

total=$(echo "$(date +%s.%N) - $t0" | bc)
printf 'total\t%.1f\t%.1f\n' "$total" "$total" >> "$timeline"
cat "$timeline"
cert="$work/plonk/plonk/proof.bin"
echo "certificate: $(stat -c %s "$cert") bytes, BLAKE3 $("$ix/toolchain-cert/bin/b3" "$cert" | cut -d' ' -f1)"
printf 'end to end: %d:%04.1f\n' "$(echo "$total / 60" | bc)" "$(echo "$total - 60 * ($total / 60)" | bc)"
