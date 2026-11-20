#!/usr/bin/env bash
# adopt_kernel.sh BRANCH : bring a kernel branch into the combined certificate's toolchain.
# Merges BRANCH into `cert` in ~/repos/forks/ix-cert, regenerates the verifying-key pins for the
# changed circuits and commits them on their own, rebuilds the toolchain, and keeps the new IxVM
# and aggregation artifacts by digest in ix/artifacts, where the `cert` profile of ix/ixw and
# certify.sh look them up from the pin file. Each long step is a gated job.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ix="$(dirname "$here")"
W=/home/sam/repos/forks/ix-cert
branch=$1
git -C $W merge --no-edit "$branch" || exit 1
"$ix/heavy.sh" "$here/update_pins.sh" || exit 1
if ! git -C $W diff --quiet -- tools/formal-aiur.keys; then
  git -C $W add tools/formal-aiur.keys
  git -C $W commit -q -m "Pin the verifying keys after merging $branch

The kernel circuit changed with the merge; the pins are regenerated from this tree."
fi
"$ix/heavy.sh" "$here/build_cert.sh" > /dev/null 2>&1 || { echo "build failed"; tail -5 /opt/dlami/nvme/ix-ai/cert/build.log; exit 1; }
ixvm=$(awk '$1 == "ixvm" { print $2 }' $W/tools/formal-aiur.keys)
aggr=$(awk '$1 == "aggregation" { print $2 }' $W/tools/formal-aiur.keys)
cp -n "$W/.lake/aiur/ixvm-$ixvm.ixa" "$ix/artifacts/ixvm-$ixvm.ixa"
cp -n /opt/dlami/nvme/ix-ai/cert/aggregate.ixa "$ix/artifacts/aggregate-$aggr.ixa"
for b in aiur_join_check export_root env_names combine_members; do
  cp /opt/dlami/nvme/ix-ai/combined/target/release/examples/$b "$ix/toolchain-cert/bin/"
done
echo "adopted $branch: ixvm $ixvm aggregation $aggr ($(git -C $W log --oneline -1 | cut -c1-60))"
