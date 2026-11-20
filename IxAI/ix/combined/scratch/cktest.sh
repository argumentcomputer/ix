#!/usr/bin/env bash
# cktest.sh: rebuild the childkind-aiur tools and run ixon's and the aggregate controller's tests.
set -uo pipefail
S=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined
export CARGO_TARGET_DIR=/opt/dlami/nvme/ix-ai/combined/target
cd /home/sam/repos/forks/ix-childkind-aiur
cap() { systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- "$@"; }
cap timeout 2600 cargo build --release --locked --offline -p ix-prover --features cuda --example aiur_join > $S/cktest.log 2>&1 \
  && cap timeout 2600 cargo build --release --locked --offline -p ix-prover --example aiur_join_check --example export_root --example combine_members >> $S/cktest.log 2>&1 \
  && cap /usr/bin/time -v -o $S/cktest.time timeout 2600 cargo test --release --locked --offline -p ixon -p aggregate-controller >> $S/cktest.log 2>&1
st=$?; grep -E "^error|^test result|FAILED|panicked" $S/cktest.log | head -40; echo "exit $st" > $S/cktest.done; exit $st
