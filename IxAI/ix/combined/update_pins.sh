#!/usr/bin/env bash
# update_pins.sh : regenerate the verifying-key pins of the combined certificate's fork
# (~/repos/forks/ix-cert, tools/formal-aiur.keys) from its own programs, as ix's
# tools/check-formal-keys.sh --update does. Run after a deliberate circuit change, then commit
# the pin file on its own and rebuild ix, which embeds it.
set -uo pipefail
W=/home/sam/repos/forks/ix-cert
N=/opt/dlami/nvme/ix-ai/cert
cd $W
# The key derivation opens the CUDA device; the nix-built library needs the system driver preloaded.
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
IX_CUDA=1 CARGO_NET_OFFLINE=true systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- \
  timeout 3600 nix develop $W --command tools/check-formal-keys.sh --update > $N/pins.log 2>&1
st=$?
tail -3 $N/pins.log
git -C $W diff --stat -- tools/formal-aiur.keys | tail -1
exit $st
