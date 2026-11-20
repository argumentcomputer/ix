#!/usr/bin/env bash
# cargobuild.sh: the combined certificate's Rust tools from the fork worktree, target on tmpfs.
set -uo pipefail
S=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined
F=/home/sam/repos/forks/ix-aiurexec-combined
export CARGO_TARGET_DIR=$S/target
cd $F
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $S/cargobuild.time timeout 2600 \
  cargo build --release --locked --offline -p stark-verifier --features stark-verifier/parallel,stark-verifier/cuda \
  --example aiur_combine --example aiur_exec --example aiur_exec_check --example b3 > $S/cargobuild.log 2>&1 || exit 1
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $S/cargobuild2.time timeout 2600 \
  cargo build --release --locked --offline -p ix-prover --example combine_members --example combine_check --example export_root >> $S/cargobuild.log 2>&1
st=$?; grep -E "^(error|warning: unused)" -A6 $S/cargobuild.log | head -60; tail -3 $S/cargobuild.log; exit $st
