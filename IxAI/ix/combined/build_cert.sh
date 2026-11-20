#!/usr/bin/env bash
# build_cert.sh : the toolchain of the combined certificate, from ~/repos/forks/ix-cert (the ci
# build of ix with the IxVM kernel fixes and the Aiur-child aggregator):
#   1. `ix`, which regenerates the IxVM artifact and the native executors from this tree;
#   2. the join tools (aiur_join with CUDA; aiur_join_check, export_root, combine_members,
#      env_names without);
#   3. the aggregation artifact (ix_aggr with the Aiur-child shapes), as ix exports it.
# Build trees are on the NVMe scratch (/opt/dlami/nvme/ix-ai/cert, and the join tools' cargo
# target in /opt/dlami/nvme/ix-ai/combined/target), so they rebuild from cold after the machine
# stops. Logs: cert/build.log, cert/tools.log, cert/aggr.log; cert/build.done holds the status.
set -uo pipefail
W=/home/sam/repos/forks/ix-cert
N=/opt/dlami/nvme/ix-ai/cert
cap() { systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- "$@"; }
rm -f $N/build.done
cd $W
IX_CUDA=1 CARGO_NET_OFFLINE=true cap timeout 5400 nix develop $W --command lake build ix > $N/build.log 2>&1
st=$?
if [ $st -eq 0 ]; then
  CARGO_TARGET_DIR=/opt/dlami/nvme/ix-ai/combined/target cap timeout 2600 cargo build --release --locked --offline \
    -p ix-prover --features cuda --example aiur_join > $N/tools.log 2>&1 \
  && CARGO_TARGET_DIR=/opt/dlami/nvme/ix-ai/combined/target cap timeout 2600 cargo build --release --locked --offline \
    -p ix-prover --example aiur_join_check --example export_root --example combine_members --example env_names >> $N/tools.log 2>&1
  st=$?
fi
if [ $st -eq 0 ]; then
  (cd $W/MultiStark && cap timeout 2600 nix develop $W --command lake build stark-export \
    && cap timeout 2600 .lake/build/bin/stark-export export-trace $N/aggregate.ixa --aggregate) > $N/aggr.log 2>&1
  st=$?
fi
echo $st > $N/build.done
tail -3 $N/build.log; tail -2 $N/tools.log 2>/dev/null; tail -2 $N/aggr.log 2>/dev/null
exit $st
