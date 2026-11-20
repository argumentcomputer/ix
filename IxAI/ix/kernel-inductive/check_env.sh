#!/usr/bin/env bash
# The constants IxVM rejected in the combined environment (reject-names.txt), checked with the
# kernel-inductive fork's ix (fixed model advice) and the pinned IxVM artifact.
P=/home/sam/repos/ix-ai-pipeline
K=$P/.truthmines/kernel-inductive
export IX_LEAN=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1 HOME=$P/.truthmines
export PATH=$IX_LEAN/bin:$PATH
# the nix-built CUDA library resolves dlopen through nix's loader, which does not search the system driver directory
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export IX_AIUR_ARTIFACT=$P/ix/artifacts/ixvm-5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576.ixa
export IX_AIUR_ARTIFACT_DIGEST=5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- timeout 5400 \
  /home/sam/repos/forks/ix-kernel-inductive/.lake/build/bin/ix check --ixe $P/.truthmines/combined/env/consts.ixe \
  --keep-going $(cat $K/reject-names.txt) > $K/check-env-fixed.log 2>&1
echo "check-env-fixed exit $?" >> $K/all.status
