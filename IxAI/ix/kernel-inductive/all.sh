#!/usr/bin/env bash
# In the kernel-inductive fork: the IxVM test tier with the current IxTests (before), the build,
# the repro checks with the rebuilt ix, then the IxVM test tier again (after).
# Logs in /home/sam/repos/ix-ai-pipeline/.truthmines/kernel-inductive/.
set -u
F=/home/sam/repos/forks/ix-kernel-inductive
N=/opt/dlami/nvme/ix-ai/kernel-inductive
K=/home/sam/repos/ix-ai-pipeline/.truthmines/kernel-inductive
P=/home/sam/repos/ix-ai-pipeline
export IX_AIUR_ARTIFACT=$P/ix/artifacts/ixvm-5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576.ixa
export IX_AIUR_ARTIFACT_DIGEST=5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576
export IX_AIUR_HOST=$N/target/release/ixvm-proof
cd $F
tests() {
  systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- timeout 5400 \
    nix develop $F --command lake env .lake/build/bin/IxTests --tier ci:ixvm > $K/tests-$1.log 2>&1
  echo "tests-$1 exit $?" >> $K/all.status
}
echo "--- all.sh $(date +%T)" >> $K/all.status
[ "${SKIP_BEFORE:-0}" = 1 ] || tests before
EXTRA_TARGETS="IxC.Kernel.Verify.Frontend.InModelGenNested IxTests" $P/ix/kernel-inductive/build.sh > /dev/null
echo "build exit $(cat $N/build.done)" >> $K/all.status
[ "$(cat $N/build.done)" = 0 ] || exit 1
# the repro checks with the rebuilt ix and the pinned artifact
cd $K/repro
( export IX_BIN=$F/.lake/build/bin/ix IX_LEAN=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1 HOME=$P/.truthmines
  export PATH=$IX_LEAN/bin:$PATH
  for f in repro repro2; do
    names=$( [ $f = repro ] && echo "KI.F2 KI.V KI.Rep KI.Ex2 KI.RepB KI.Q KI.Vec KI.T" || echo "KJ.F2 KJ.W KJ.RepW KJ.NB KJ.NC KJ.Plain")
    timeout 1800 $IX_BIN check --ixe $f.ixe --keep-going $names > check-$f-fixed.log 2>&1
    echo "check-$f-fixed exit $?" >> $K/all.status
  done )
cd $F
tests after
