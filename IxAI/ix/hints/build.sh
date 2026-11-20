#!/usr/bin/env bash
# Build the instrumented `ix` in the kernel-hints worktree (build trees on the NVMe) inside the
# repo's nix dev shell. Writes build.done with lake's exit status when finished.
N=/opt/dlami/nvme/ix-ai/kernel-hints
rm -f $N/build.done
cd /home/sam/repos/forks/ix-kernel-hints
df -h / /opt/dlami/nvme > $N/build.log 2>&1
IX_CUDA=1 CARGO_NET_OFFLINE=true /usr/bin/time -v systemd-run --user --scope -q -p MemoryMax=180G -- \
  timeout 5400 nix develop /home/sam/repos/forks/ix-kernel-hints --command lake build ix >> $N/build.log 2>&1
st=$?
df -h / /opt/dlami/nvme >> $N/build.log 2>&1
echo "$st" > $N/build.done
exit 0
