#!/usr/bin/env bash
# The repro constants checked with the kernel-inductive fork's ix and the pinned IxVM artifact.
P=/home/sam/repos/ix-ai-pipeline
K=$P/.truthmines/kernel-inductive
export IX_LEAN=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1 HOME=$P/.truthmines
export PATH=$IX_LEAN/bin:$PATH
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export IX_AIUR_ARTIFACT=$P/ix/artifacts/ixvm-5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576.ixa
export IX_AIUR_ARTIFACT_DIGEST=5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576
B=/home/sam/repos/forks/ix-kernel-inductive/.lake/build/bin/ix
cd $K/repro
timeout 1800 $B check --ixe repro.ixe --keep-going KI.F2 KI.V KI.Rep KI.Ex2 KI.RepB KI.Q KI.Vec KI.T > check-repro-fixed.log 2>&1
echo "check-repro-fixed exit $?" >> $K/all.status
timeout 1800 $B check --ixe repro2.ixe --keep-going KJ.F2 KJ.W KJ.RepW KJ.NB KJ.NC KJ.Plain > check-repro2-fixed.log 2>&1
echo "check-repro2-fixed exit $?" >> $K/all.status
