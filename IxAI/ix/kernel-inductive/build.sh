#!/usr/bin/env bash
# Build `ix` and the modeller's renaming proof in the kernel-inductive fork (build trees on the
# NVMe) inside the fork's nix dev shell. Writes build.log and build.done (lake's exit status).
N=/opt/dlami/nvme/ix-ai/kernel-inductive
rm -f $N/build.done
cd /home/sam/repos/forks/ix-kernel-inductive
IX_CUDA=1 CARGO_NET_OFFLINE=true /usr/bin/time -v -o $N/build.time systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- \
  timeout "${BUILD_CAP:-5400}" nix develop /home/sam/repos/forks/ix-kernel-inductive --command \
  lake build ix ${EXTRA_TARGETS:-IxC.Kernel.Verify.Frontend.InModelGenNested} > $N/build.log 2>&1
echo $? > $N/build.done
tail -30 $N/build.log
