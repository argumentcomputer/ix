#!/usr/bin/env bash
# Identical claim streams and identical recursive proof inputs; both executors
# are bytecode. Compile/setup/IO preparation are outside the execution timer.
set -euo pipefail
cd "$(dirname "$0")/../.."
comparison_dir=${1:-.lake/formal-comparison}
mkdir -p "$comparison_dir"
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-1}
export IX_BENCH_NO_THP=${IX_BENCH_NO_THP:-1}
samples=${IX_BENCH_SAMPLES:-5}
lake build bench-compare-aiur formal-aiur-tests ixvm/ixvm multiStark/stark-export
cargo build --release --locked -p stark-verifier --features parallel --example compare --bin stark-verifier
if [[ -z ${IX_AIUR_ARTIFACT:-} ]]; then
  IX_AIUR_ARTIFACT="$comparison_dir/ixvm.json"
  lake env IxVM/.lake/build/bin/ixvm export-claim-trace "$IX_AIUR_ARTIFACT"
fi
if [[ -z ${IX_RECURSION_ARTIFACT:-} ]]; then
  IX_RECURSION_ARTIFACT="$comparison_dir/recursion.json"
  lake env MultiStark/.lake/build/bin/stark-export export-trace "$IX_RECURSION_ARTIFACT"
fi
lake env .lake/build/bin/formal-aiur-tests "$comparison_dir/claims.json"
python3 - "$comparison_dir" <<'PY'
import json, pathlib, sys
p = pathlib.Path(sys.argv[1])
cases = json.loads((p / 'claims.json').read_text())
for target, label in [('ixvm', 'CheckEnv frontier-asm (Nat.add_comm)'),
                      ('environment', 'CheckEnv self-contained (shared smoke env)')]:
    case = next(c for c in cases if c['label'] == label)
    (p / (target + '-input.json')).write_text(json.dumps(case['invocation']))
PY
target/release/stark-verifier fixture "$comparison_dir/recursive-fixture"
for workload in ixvm environment recursion; do
  app=ixvm
  artifact="$IX_AIUR_ARTIFACT"
  input="$comparison_dir/$workload-input.json"
  if [[ $workload == recursion ]]; then
    app=recursion
    artifact="$IX_RECURSION_ARTIFACT"
    input="$comparison_dir/recursive-fixture/input.json"
  fi
  for grouping in grouped ungrouped; do
    flags=()
    [[ $grouping == grouped ]] || flags+=(--ungrouped)
    .lake/build/bin/bench-compare-aiur "$app" "$input" \
      "$comparison_dir/legacy-$workload-$grouping.json" "$samples" --prove "${flags[@]}"
    target/release/examples/compare "$artifact" "$input" \
      "$comparison_dir/new-$workload-$grouping.json" "$samples" --prove --save-proof "${flags[@]}"
  done
done
# Reuse one real IxVM proof for both recursive interpreters. Proving this much
# larger verifier trace is optional; its execution/trace/cell comparison is on
# by default. The tiny fixture above exercises both outer provers regardless.
input="$comparison_dir/new-environment-grouped.json.inner/input.json"
flags=()
[[ ${IX_BENCH_RECURSIVE_PROVE:-0} == 0 ]] || flags+=(--prove)
for grouping in grouped ungrouped; do
  group_flags=()
  [[ $grouping == grouped ]] || group_flags+=(--ungrouped)
  .lake/build/bin/bench-compare-aiur recursion "$input" \
    "$comparison_dir/legacy-recursion-real-$grouping.json" "${IX_BENCH_REAL_SAMPLES:-3}" "${flags[@]}" "${group_flags[@]}"
  target/release/examples/compare "$IX_RECURSION_ARTIFACT" "$input" \
    "$comparison_dir/new-recursion-real-$grouping.json" "${IX_BENCH_REAL_SAMPLES:-3}" "${flags[@]}" "${group_flags[@]}"
done
python3 tools/ixvm/compare-results.py "$comparison_dir" "$IX_AIUR_ARTIFACT" "$IX_RECURSION_ARTIFACT"
