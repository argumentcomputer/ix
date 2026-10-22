#!/usr/bin/env bash
# Integration gate for the separate packages. Existing exported artifacts can
# be supplied through the three IX_*_ARTIFACT variables to reuse compilation.
set -euo pipefail
cd "$(dirname "$0")/../.."
formal_tmp=$(mktemp -d)
trap 'rm -rf "$formal_tmp"' EXIT

python3 tools/ixvm/adapt.py --check
python3 tools/ixvm/recursion.py --check
python3 tools/ixvm/recursion.py --aggregate --check
lake build ix ixvm/ixvm multiStark/stark-export formal-aiur-tests formal-aggregate-tests
cargo build --release --locked -p ixvm -p stark-verifier --features parallel \
  --bin ixvm-proof --bin stark-verifier --example claim_fixture

if [[ -z ${IX_AIUR_ARTIFACT:-} ]]; then
  IX_AIUR_ARTIFACT="$formal_tmp/ixvm.json"
  lake env IxVM/.lake/build/bin/ixvm export-claim-trace "$IX_AIUR_ARTIFACT"
fi
if [[ -z ${IX_RECURSION_ARTIFACT:-} ]]; then
  IX_RECURSION_ARTIFACT="$formal_tmp/recursion.json"
  lake env MultiStark/.lake/build/bin/stark-export export-trace "$IX_RECURSION_ARTIFACT"
fi
if [[ -z ${IX_AGGR_ARTIFACT:-} ]]; then
  IX_AGGR_ARTIFACT="$formal_tmp/aggregate.json"
  lake env MultiStark/.lake/build/bin/stark-export export-trace "$IX_AGGR_ARTIFACT" --aggregate
fi
export IX_AIUR_ARTIFACT IX_AGGR_ARTIFACT

lake env .lake/build/bin/formal-aiur-tests "$formal_tmp/claims.json"
target/release/ixvm-proof test "$IX_AIUR_ARTIFACT" "$formal_tmp/claims.json"
.lake/build/bin/ix check --formal --ixe "$formal_tmp/claims.json.ixe" Nat.add_comm
.lake/build/bin/ix prove --formal Nat.add_comm > "$formal_tmp/prove.log"
cat "$formal_tmp/prove.log"
formal_proof=$(tail -n 1 "$formal_tmp/prove.log")
.lake/build/bin/ix verify --formal "$formal_proof"

target/release/stark-verifier fixture "$formal_tmp/inner"
target/release/stark-verifier test "$IX_RECURSION_ARTIFACT" "$formal_tmp/inner/input.json"
target/release/stark-verifier prove "$IX_RECURSION_ARTIFACT" "$formal_tmp/inner/input.json" "$formal_tmp/outer"
target/release/stark-verifier verify "$IX_RECURSION_ARTIFACT" "$formal_tmp/outer/public.json" "$formal_tmp/outer/proof.bin"
.lake/build/bin/formal-aggregate-tests "$formal_tmp/aggregation.json"
target/release/stark-verifier cases "$IX_AGGR_ARTIFACT" "$formal_tmp/aggregation.json"
target/release/stark-verifier prove "$IX_AGGR_ARTIFACT" "$formal_tmp/aggregation.json.wrap.json" "$formal_tmp/aggregate"
target/release/stark-verifier verify "$IX_AGGR_ARTIFACT" "$formal_tmp/aggregate/public.json" "$formal_tmp/aggregate/proof.bin"
