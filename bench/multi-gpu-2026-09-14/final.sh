#!/bin/sh
# final.sh [GPU]: after every lane has exited 0, the composed verdict over all
# claim proofs, the final aggregate (the lanes' subtree roots are cache hits;
# only the joins above them and the root wraps are proven), and the root
# verify. Run from the run directory with IX, IXE and IXES set.
set -eu
. "$(dirname "$0")/lanelib.sh"
g=${1:-0}
export CUDA_VISIBLE_DEVICES=$g MULTI_STARK_CUDA_DEVICE=0

cat lane?-proofs.txt > proofs.txt
echo "final: $(wc -l < proofs.txt) claim proofs"
# No pipe: a failed composed verdict must stop the script.
# shellcheck disable=SC2046
"$IX" verify --ixe "$IXE" --ixes "$IXES" $(cat proofs.txt) > verify-claims.log 2>&1
tail -1 verify-claims.log

# shellcheck disable=SC2046
run 0-95 "$IX" aggregate --ixe "$IXE" --ixes "$IXES" $STAGE2_FLAGS \
  --jobs 1 --max-ram 200 --wrap-root $(cat proofs.txt) > final.log 2> final.err
# The root address is reported on stderr; the command's stdout carries none.
ROOT=$(sed -n 's/^\[aggregate\] root proof: \([0-9a-f]\{64\}\).*/\1/p' final.err | tail -1)
echo "final: cached subtree roots: $(grep -c 'cached; its subtree is not visited' final.err); joins proven: $(grep -c 'joining slots' final.err)"
[ -n "$ROOT" ] || { echo "final: no root proof address in final.err" >&2; exit 1; }
echo "final: root $ROOT"
# No pipe here: the verifier's own exit status must be the script's.
"$IX" verify --aggregate --structural-above 0 --ixe "$IXE" --ixes "$IXES" "$ROOT" > verify-root.log 2>&1
tail -1 verify-root.log
