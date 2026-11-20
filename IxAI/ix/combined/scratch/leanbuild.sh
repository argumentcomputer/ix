#!/usr/bin/env bash
# leanbuild.sh TARGET...: lake build in the combined environment's source snapshot, timed, capped.
set -uo pipefail
cd /home/sam/repos/ix-ai-pipeline/.truthmines/combined/src/Aiur
export PATH=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1/bin:$PATH
S=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/combined
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $S/leanbuild.time timeout 2600 lake build "$@" > $S/leanbuild.log 2>&1
st=$?; tail -5 $S/leanbuild.log; exit $st
