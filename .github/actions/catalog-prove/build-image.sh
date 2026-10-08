#!/usr/bin/env bash
# Build the prover image from an ix checkout whose CUDA binary is already
# built (`lake build ix`). The image is tagged with the binary's sha256
# prefix, the same executable identity the proving profile pins.
#
#   build-image.sh <ix-checkout>
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <ix-checkout>" >&2
  exit 2
fi
checkout=$1
here=$(dirname "$(realpath "$0")")

context=$(mktemp -d)
trap 'rm -rf "$context"' EXIT
install -m 0755 "$checkout/.lake/build/bin/ix" "$context/ix"
cp "$checkout/lean-toolchain" "$context/lean-toolchain"

hash=$(sha256sum "$context/ix" | cut -c1-16)
tag="ix-prover:$hash"
docker build -f "$here/Dockerfile" -t "$tag" "$context"
echo "$tag"
