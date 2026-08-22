#!/usr/bin/env bash
set -euo pipefail

readonly expected_revision="c98bb74106017e518c705b2567f022e89f732393"
readonly ix_dir="$(realpath "${1:?usage: $0 /path/to/ix}")"
readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly template_dir="${script_dir}/ix-sharing-baseline"

if [[ "$(git -C "${ix_dir}" rev-parse HEAD)" != "${expected_revision}" ]]; then
  echo "error: ix checkout is not at ${expected_revision}" >&2
  exit 1
fi

readonly relevant_paths=(
  Ix/Address.lean
  Ix/Ixon.lean
  Ix/Sharing.lean
  Tests/Ix/Sharing.lean
  crates/ffi/src/lean_ixon/sharing.rs
  crates/ixon/src
)
if ! git -C "${ix_dir}" diff --quiet HEAD -- "${relevant_paths[@]}"; then
  echo "error: ix sharing baseline files have local changes" >&2
  exit 1
fi

readonly runner_dir="$(mktemp -d)"
cleanup() {
  rm -rf -- "${runner_dir}"
}
trap cleanup EXIT

cp "${template_dir}/lean-toolchain" "${runner_dir}/lean-toolchain"
cp "${template_dir}/lakefile.lean" "${runner_dir}/lakefile.lean"
cp "${template_dir}/Main.lean" "${runner_dir}/Main.lean"
ln -s "${ix_dir}" "${runner_dir}/ix"
if [[ -d "${ix_dir}/.lake/packages" ]]; then
  mkdir -p "${runner_dir}/.lake"
  ln -s "${ix_dir}/.lake/packages" "${runner_dir}/.lake/packages"
fi

(
  cd "${ix_dir}"
  nix develop --command cargo build --release -p ix-ffi \
    --features parallel,test-ffi
)
cp "${ix_dir}/target/release/libix_ffi.a" \
  "${runner_dir}/libix_ffi_test.a"

(
  cd "${runner_dir}"
  nix develop "${ix_dir}" --command lake build parity
  .lake/build/bin/parity
)
