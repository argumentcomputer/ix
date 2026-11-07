#!/usr/bin/env bash
# Integration gate for the separate packages. Existing exported artifacts can
# be supplied through the three IX_*_ARTIFACT variables to reuse compilation.
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ -n ${IX_TEST_OUTPUT_DIR:-} ]]; then
  mkdir -p "$IX_TEST_OUTPUT_DIR"
  formal_tmp=$(realpath "$IX_TEST_OUTPUT_DIR")
elif [[ ${IX_TEST_CUDA:-0} == 1 ]]; then
  mkdir -p .lake
  formal_tmp=$(mktemp -d "$PWD/.lake/formal-cuda-check.XXXXXX")
else
  formal_tmp=$(mktemp -d)
  trap 'rm -rf "$formal_tmp"' EXIT
fi
# Proving environment settings must not switch the baseline CLI to CUDA or
# poison its CPU-only witness generation. The hardware gate scopes them itself.
export IX_CUDA=0 AIUR_TRACE_ONLY_LOOKUPS=0

lake build ix ixvm/ixvm multiStark/stark-export formal-aiur-tests formal-aggregate-tests formal-checks \
  aiur/grouping_example aiur/Aiur.Library.U8Facts
# The IxVM and MultiStark modules are Lean source (`aiur⟦ … ⟧`). Only
# IxVM/IxVM/Modules/KernelRoleSpec.lean is rendered, from IxC's role specifications.
.lake/build/bin/ix codegen --check
lake env Aiur/.lake/build/bin/grouping_example crates/aiur/tests/fixtures/grouping.ixa --check
cargo build --release --locked -p ixvm -p stark-verifier -p ix-prover --features parallel \
  --bin ixvm-proof --bin stark-verifier --bin ix-prover --example claim_fixture

if [[ -z ${IX_AIUR_ARTIFACT:-} ]]; then
  IX_AIUR_ARTIFACT="$formal_tmp/ixvm.ixa"
  lake env IxVM/.lake/build/bin/ixvm export-claim-trace "$IX_AIUR_ARTIFACT"
fi
if [[ -z ${IX_RECURSION_ARTIFACT:-} ]]; then
  IX_RECURSION_ARTIFACT="$formal_tmp/recursion.ixa"
  lake env MultiStark/.lake/build/bin/stark-export export-trace "$IX_RECURSION_ARTIFACT"
fi
if [[ -z ${IX_AGGR_ARTIFACT:-} ]]; then
  IX_AGGR_ARTIFACT="$formal_tmp/aggregate.ixa"
  lake env MultiStark/.lake/build/bin/stark-export export-trace "$IX_AGGR_ARTIFACT" --aggregate
fi
export IX_AIUR_ARTIFACT IX_AGGR_ARTIFACT

lake env .lake/build/bin/formal-aiur-tests "$formal_tmp/claims.ixt"
target/release/ixvm-proof test "$IX_AIUR_ARTIFACT" "$formal_tmp/claims.ixt"
.lake/build/bin/ix check --ixe "$formal_tmp/claims.ixt.ixe" Nat.add_comm
.lake/build/bin/ix prove Nat.add_comm > "$formal_tmp/prove.log"
cat "$formal_tmp/prove.log"
formal_proof=$(tail -n 1 "$formal_tmp/prove.log")
.lake/build/bin/ix verify "$formal_proof"
AIUR_TRACE_ONLY_LOOKUPS=1 .lake/build/bin/ix verify "$formal_proof"

target/release/stark-verifier fixture "$formal_tmp/inner"
target/release/stark-verifier ranges "$formal_tmp/inner/proof.bin" "$formal_tmp/ranges" 1
.lake/build/bin/formal-checks ranges "$formal_tmp"
target/release/stark-verifier test "$IX_RECURSION_ARTIFACT" "$formal_tmp/inner/input.ixi"
target/release/stark-verifier prove "$IX_RECURSION_ARTIFACT" "$formal_tmp/inner/input.ixi" "$formal_tmp/outer"
target/release/stark-verifier verify "$IX_RECURSION_ARTIFACT" "$formal_tmp/outer/public.ixi" "$formal_tmp/outer/proof.bin"
AIUR_TRACE_ONLY_LOOKUPS=1 target/release/stark-verifier verify "$IX_RECURSION_ARTIFACT" "$formal_tmp/outer/public.ixi" "$formal_tmp/outer/proof.bin"
.lake/build/bin/formal-aggregate-tests "$formal_tmp/aggregation.ixt"
target/release/stark-verifier cases "$IX_AGGR_ARTIFACT" "$formal_tmp/aggregation.ixt"
target/release/stark-verifier prove "$IX_AGGR_ARTIFACT" "$formal_tmp/aggregation.ixt.wrap.ixi" "$formal_tmp/aggregate"
target/release/stark-verifier verify "$IX_AGGR_ARTIFACT" "$formal_tmp/aggregate/public.ixi" "$formal_tmp/aggregate/proof.bin"

.lake/build/bin/formal-checks controller "$formal_tmp" \
  --ixvm-artifact "$IX_AIUR_ARTIFACT" \
  --recursion-artifact "$IX_RECURSION_ARTIFACT" \
  --aggregate-artifact "$IX_AGGR_ARTIFACT"

# Optional hardware gate: prove with CUDA and independently verify with CPU
# binaries. The separate target directory is the same one the CLI selects.
cuda_check_args=()
if [[ ${IX_TEST_CUDA:-0} == 1 ]]; then
  cargo build --release --locked --target-dir target/formal-cuda \
    -p ixvm -p stark-verifier -p ix-prover --features parallel,cuda --bin ixvm-proof --bin stark-verifier --bin ix-prover
  .lake/build/bin/formal-checks controller "$formal_tmp" \
    --ixvm-artifact "$IX_AIUR_ARTIFACT" \
    --recursion-artifact "$IX_RECURSION_ARTIFACT" \
    --aggregate-artifact "$IX_AGGR_ARTIFACT" --devices "${MULTI_STARK_CUDA_DEVICE:-0}"
else
  cuda_check_args+=(--cpu-only)
fi
.lake/build/bin/formal-checks cuda "$formal_tmp" \
  --ixvm-artifact "$IX_AIUR_ARTIFACT" \
  --recursion-artifact "$IX_RECURSION_ARTIFACT" \
  --aggregate-artifact "$IX_AGGR_ARTIFACT" "${cuda_check_args[@]}"
