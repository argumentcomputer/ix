#!/usr/bin/env bash
# msbuild.sh: build aiurexec-export (with the AiurCombine instance) in the fork worktree and export
# the combine package.
set -uo pipefail
S=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined
F=/home/sam/repos/forks/ix-aiurexec-combined
cd $F/MultiStark
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $S/msbuild.time \
  timeout 2600 nix develop $F --command lake build aiurexec-export > $S/msbuild.log 2>&1 || { tail -30 $S/msbuild.log; exit 1; }
mkdir -p $S/exports
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $S/cbexport.time \
  timeout 2600 .lake/build/bin/aiurexec-export export $S/exports/aiur-combine.ixa --combine > $S/cbexport.log 2>&1
st=$?; tail -3 $S/cbexport.log; exit $st
