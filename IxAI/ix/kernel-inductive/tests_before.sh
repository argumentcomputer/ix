#!/usr/bin/env bash
# The IxVM test tier (ci:ixvm) with the de5970000 build of IxTests in ~/repos/ix.ci-merge-tests,
# used read-only (its build trees on LEAN_PATH; no lake invocation), against the pinned artifact.
C=/home/sam/repos/ix.ci-merge-tests
P=/home/sam/repos/ix-ai-pipeline
K=$P/.truthmines/kernel-inductive
L=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1
lp=$L/lib/lean:$C/.lake/build/lib/lean
for d in $C/.lake/kernel/lib/lean $C/.lake/packages/*/.lake/build/lib/lean $C/Aiur/.lake/build/lib/lean $C/IxVM/.lake/build/lib/lean $C/MultiStark/.lake/build/lib/lean; do lp=$lp:$d; done
export LEAN_PATH=$lp PATH=$L/bin:$PATH
export IX_AIUR_ARTIFACT=$P/ix/artifacts/ixvm-5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576.ixa
export IX_AIUR_ARTIFACT_DIGEST=5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576
export IX_AIUR_HOST=$C/target/release/ixvm-proof
d=$(mktemp -d); for e in $C/* ; do ln -s $e $d/; done; cd $d
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- timeout 5400 \
  $C/.lake/build/bin/IxTests --tier ci:ixvm > $K/tests-before.log 2>&1
echo "tests-before (ci-merge-tests IxTests) exit $?" >> $K/all.status
