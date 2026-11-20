#!/usr/bin/env bash
# ckbuild.sh [test]: the childkind-aiur Rust tools (target on nvme); with `test`, the aggregate
# controller's and ixon's unit tests.
set -uo pipefail
S=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined
export CARGO_TARGET_DIR=/opt/dlami/nvme/ix-ai/combined/target
cd /home/sam/repos/forks/ix-childkind-aiur
cap() { systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- "$@"; }
if [ "${1:-}" = test ]; then
  cap /usr/bin/time -v -o $S/cktest.time timeout 2600 cargo test --release --locked --offline -p ixon -p aggregate-controller > $S/cktest.log 2>&1
  st=$?; grep -E "^test result|FAILED|panicked" $S/cktest.log | head -30; exit $st
fi
cap /usr/bin/time -v -o $S/ckbuild.time timeout 2600 cargo build --release --locked --offline -p ix-prover --features cuda \
  --example aiur_join --example export_root --example combine_members > $S/ckbuild.log 2>&1
st=$?; grep -E "^error" -A12 $S/ckbuild.log | head -80; tail -2 $S/ckbuild.log; exit $st
