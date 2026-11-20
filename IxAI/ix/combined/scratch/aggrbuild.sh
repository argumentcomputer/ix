#!/usr/bin/env bash
# aggrbuild.sh: build stark-export in the childkind-aiur worktree and export the aggregation
# artifact (ix_aggr with the Aiur-child shapes), as ix exports it (export-trace --aggregate).
set -uo pipefail
W=/home/sam/repos/forks/ix-childkind-aiur
mkdir -p /opt/dlami/nvme/ix-ai/combined/exports
cd $W/MultiStark
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o /tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined/aggrbuild.time \
  timeout 2600 nix develop $W --command lake build stark-export > /tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined/aggrbuild.log 2>&1 || { grep -B2 -A10 "error" /tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined/aggrbuild.log | head -60; exit 1; }
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o /tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined/aggrexport.time \
  timeout 2600 .lake/build/bin/stark-export export-trace /opt/dlami/nvme/ix-ai/combined/exports/aggregate-new.ixa --aggregate > /tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined/aggrexport.log 2>&1
st=$?; tail -3 /tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined/aggrexport.log; exit $st
