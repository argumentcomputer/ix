#!/usr/bin/env bash
# build_tools.sh : the join tools from the Aiur-child fork (~/repos/forks/ix-childkind-aiur):
# aiur_join with CUDA, then aiur_join_check, export_root, combine_members and env_names without. The cargo
# target is on the NVMe scratch, so it is rebuilt from cold after the machine stops; the log is
# next to it.
set -uo pipefail
N=/opt/dlami/nvme/ix-ai/combined
export CARGO_TARGET_DIR=$N/target
cd /home/sam/repos/forks/ix-childkind-aiur
cap() { systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- "$@"; }
cap timeout 2600 cargo build --release --locked --offline -p ix-prover --features cuda --example aiur_join > $N/tools.log 2>&1 \
  && cap timeout 2600 cargo build --release --locked --offline -p ix-prover \
       --example aiur_join_check --example export_root --example combine_members --example env_names >> $N/tools.log 2>&1
st=$?
grep -E "^error" -A12 $N/tools.log | head -60
tail -2 $N/tools.log
exit $st
