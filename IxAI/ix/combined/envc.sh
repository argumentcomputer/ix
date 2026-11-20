#!/usr/bin/env bash
# envc.sh VARIANT: certified compile of the combined environment with phase timings (-v),
# 24 workers, output and logs on the NVMe scratch. VARIANT: consts (T, B and the safety
# theorems with their closure), assumed (the same with T an axiom: B's closure holds the
# statement but not its proof), deployed (consts plus the deployed model, its card and its gate
# decisions), local (--local), whole (the whole import environment).
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
N=/opt/dlami/nvme/ix-ai/combined/compile
SRC=$P/.truthmines/combined/src/Aiur
cd $SRC
file=IxAICombined.lean
case "$1" in
  consts) flags=(--consts IxAICombined.train_of_deployed_blocks_enc,IxAICombined.blockRun,IxAICombined.publish_sound,IxAICombined.publish_confident,IxAICombined.defer_iff) ;;
  assumed) file=IxAICombined/Assumed.lean
    flags=(--consts IxAICombined.Assumed.train_of_deployed_blocks_enc,IxAICombined.Assumed.blockRun,IxAICombined.publish_sound,IxAICombined.publish_confident,IxAICombined.defer_iff) ;;
  deployed) file=IxAICombined/Deployed.lean
    flags=(--consts IxAICombined.train_of_deployed_blocks_enc,IxAICombined.blockRun,IxAICombined.publish_sound,IxAICombined.publish_confident,IxAICombined.defer_iff,IxAICombined.Deployed.trainedOutput,IxAICombined.Deployed.cardOutput,IxAICombined.Deployed.cardCertified,IxAICombined.Deployed.decision0,IxAICombined.Deployed.decision1,IxAICombined.Deployed.decision2,IxAICombined.Deployed.decision3,IxAICombined.Deployed.deployedPublishSound,IxAICombined.Deployed.deployedPublishConfident,IxAICombined.Deployed.deployedDeferIff,IxAICombined.Deployed.config_eq,IxAICombined.Deployed.trainedOutput_ok) ;;
  local) flags=(--local) ;;
  whole) flags=() ;;
  *) echo "unknown variant"; exit 2 ;;
esac
export IX_PROFILE="${IX_PROFILE:-ci}"
nvidia-smi >/dev/null 2>&1 || true
( while sleep 30; do echo "$(date +%T) $(ps -o rss=,etime=,time= -C ix | head -1)"; done ) > $N/$1.rss &
mon=$!
systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- /usr/bin/time -v -o $N/$1.time \
  timeout 2700 stdbuf -oL -eL $P/ix/ixw compile $file "${flags[@]}" --no-build -v --workers 24 \
  --out $N/$1.ixe --report $N/$1.json > $N/$1.log 2>&1
st=$?; kill $mon; tail -15 $N/$1.log; grep -E "Elapsed|Maximum" $N/$1.time; exit $st
