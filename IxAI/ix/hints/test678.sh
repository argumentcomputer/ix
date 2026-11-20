#!/usr/bin/env bash
# test678.sh : the kernel of ix pull request 678 on this project's problem cases. Results go to
# .truthmines/kernel-678: the core-only reproduction, the two expensive unfolding lemmas, and
# the inductive types the pinned kernel rejects (with two constants it accepts as controls).
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
K=$P/.truthmines/kernel-678
N=/opt/dlami/nvme/ix-ai/pr678
SRC=$P/.truthmines/combined/src/Aiur
X=$P/ix/hints/ix678
cap() { systemd-run --user --scope -q -p MemoryMax=170G -p MemorySwapMax=0 -- "$@"; }
# The first check compiles and caches this checkout's IxVM; run it alone.
cap timeout 1500 $X check --ixe $K/repro678.ixe --keep-going Repro.Tree Repro.Forall2 Repro.Rel \
  Repro.gen Repro.gen.eq_def > $K/repro678.check.log 2>&1
echo "repro check exit $?"
(cd $SRC && cap timeout 600 $X compile EqDefRepro.lean \
  --consts IxAICore.Formula.gen.eq_def,IxAICore.shuffleAux.eq_def,IxAICore.Formula.gen.eq_2 \
  --no-build --out $K/eqdef678.ixe > $K/eqdef678.compile.log 2>&1)
echo "eqdef compile exit $?"
rm -rf $K/eqdef678.out
IXW=$X cap python3 $P/ix/combined/check_consts.py $K/eqdef678.ixe $K/eqdef.names $K/eqdef678.out \
  --jobs 2 --cap 300 --mem 60
(cd $SRC && cap timeout 900 $X compile IxAICombined.lean \
  --consts IxAICombined.train_of_deployed_blocks_enc,IxAICombined.blockRun,IxAICombined.publish_sound,IxAICombined.publish_confident,IxAICombined.defer_iff \
  --no-build --workers 24 --out $N/consts678.ixe --report $K/consts678.json > $K/consts678.compile.log 2>&1)
echo "consts compile exit $?"
rm -rf $K/inductive678.out
IXW=$X cap python3 $P/ix/combined/check_consts.py $N/consts678.ixe $K/inductive.names $K/inductive678.out \
  --jobs 3 --cap 300 --mem 50
echo done > $K/test678.done
