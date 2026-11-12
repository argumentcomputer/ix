#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

targets=(
  aiur/bn254_execution_fixture aiur/bn254_trace_fixture
  aiur/bn254_grouped_fixture aiur/bn254_gap_fixture aiur/bn254_inactive_fixture
  aiur/bn254_fq_fixture aiur/bn254_g1_fixture aiur/bn254_g1_encoding_fixture
  aiur/bn254_fq_products_fixture aiur/bn254_pairing_fixture
  aiur/bn254_preparation_check aiur/emulated_goldilocks_fixture aiur/wide_artifact_fixture
  multiStark/kzg_xof_fixture multiStark/kzg_source_fixture
  multiStark/compress_final_export multiStark/MultiStark
)
lake build --wfail "${targets[@]}"
fixtures=crates/aiur/tests/fixtures
while read -r executable artifact; do
  lake env "Aiur/.lake/build/bin/$executable" "$fixtures/$artifact.ixa" --check
done <<'FIXTURES'
bn254_execution_fixture bn254-execution
bn254_trace_fixture bn254-trace
bn254_grouped_fixture bn254-grouped
bn254_gap_fixture bn254-gap
bn254_inactive_fixture bn254-inactive
bn254_fq_fixture bn254-fq
bn254_g1_fixture bn254-g1
bn254_g1_encoding_fixture bn254-g1-encoding
bn254_fq_products_fixture bn254-fq-products
emulated_goldilocks_fixture goldilocks-emulated
wide_artifact_fixture bn254-wide
FIXTURES
lake env MultiStark/.lake/build/bin/kzg_xof_fixture "$fixtures/kzg-xof.ixa" --check
lake env MultiStark/.lake/build/bin/kzg_source_fixture "$fixtures/kzg-source.ixa" --check

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cargo run --release --locked -p ix-proof-compression --example aiur_pairing_lines -- "$scratch/generator"
cargo run --release --locked -p ix-proof-compression --example aiur_pairing_lines -- "$scratch/ignition" --ignition
cargo run --release --locked -p ix-proof-compression --example aiur_final_fixture -- "$scratch/final"
cmp "$scratch/final/configuration.json" "$fixtures/compress-final.json"
lake env MultiStark/.lake/build/bin/compress_final_export \
  "$fixtures/compress-final.json" "$fixtures/compress-final.ixa" --check
for kind in generator ignition; do
  prefix=bn254-pairing
  if [[ $kind == ignition ]]; then prefix=bn254-pairing-ignition; fi
  cmp "$scratch/$kind/lines.txt" "$fixtures/$prefix-lines.txt"
  cmp "$scratch/$kind/provenance.json" "$fixtures/$prefix-lines.json"
  lake env Aiur/.lake/build/bin/bn254_preparation_check \
    "$fixtures/$prefix-lines.json" "$fixtures/$prefix-lines.txt"
  lake env Aiur/.lake/build/bin/bn254_pairing_fixture \
    "$fixtures/$prefix-lines.txt" "$fixtures/$prefix.ixa" --check
done
