#!/usr/bin/env bash
# rebuild_env.sh TARGET... : lake build in the combined environment's source snapshot, timed and
# memory-capped. Writes leanbuild.{log,time,done} on the NVMe; `done` holds the exit status.
set -uo pipefail
N=/opt/dlami/nvme/ix-ai/combined
cd /home/sam/repos/ix-ai-pipeline/.truthmines/combined/src/Aiur
export PATH=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1/bin:$PATH
rm -f $N/leanbuild.done
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- \
  /usr/bin/time -v -o $N/leanbuild.time timeout 3000 lake build "$@" > $N/leanbuild.log 2>&1
st=$?
echo $st > $N/leanbuild.done
exit $st
