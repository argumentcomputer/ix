#!/usr/bin/env bash
# Release-consistency gate: re-derive, from the checkout
# and with no cache, the bundled verifying keys `ix verify` trusts by default,
# and compare every pin they fix.
#
#   tools/rederive-release-keys.sh IXVM_KEY_DIR AGGR_KEY_DIR WORK_DIR
#
# IXVM_KEY_DIR and AGGR_KEY_DIR are the `ixvm-proof key` and `stark-verifier
# key` directories of the release's IxVM and aggregation artifacts (see
# crates/proof-compression/README.md, "The formal artifacts and their keys").
# WORK_DIR must not exist: it receives HOME, TMPDIR, the parameter directory,
# the cargo target directory and every cache of the run, so no cached entry can
# reach the derivation. The Ignition SRS (4.1 GB) is downloaded into it, or
# copied from IX_RELEASE_SRS, and its SHA-256 is checked against the pin.
# Cargo's registry is read from its usual place.
#
# Checks (tests of crates/proof-compression; the ignored ones run only here):
# 1. the bundled release files match their pins, and the exported recursive
#    verifier description matches its pin (`bundled_release_files_match_their_pins`,
#    `release_plonk_description_matches_its_pin`);
# 2. ROOT_VK_BLAKE3, STATEMENT_PREFIX and the layout's key binding follow from
#    the two keys (`release_prefix_matches_the_release_keys`);
# 3. the recursive key derived from the aggregation key, the bundled layout and
#    the pin-checked SRS is `recursive-vk.bin` byte for byte, so
#    RECURSIVE_VK_BLAKE3 and RECURSIVE_VK_ID hold too
#    (`release_recursive_key_derives_without_a_proof`; measured for 0.5:
#    1,190 s and 115.6 GB peak RSS at 16 threads).
#
# Needs about 120 GB of available memory (it refuses to start below MIN_MEM_GB,
# default 120, of MemAvailable) and about 30 GB of disk.
# The log is WORK_DIR/rederive.log; keep it with the release.
set -euo pipefail
[ $# -eq 3 ] || { sed -n '2,31p' "$0" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && pwd)
ixvm=$(cd "$1" && pwd)
aggr=$(cd "$2" && pwd)
work=$3
srs_url=https://argument-kzg-params-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/bn254/ignition/main-197/srs.bin
srs_sha256=$(grep -A1 'const IGNITION_SRS_SHA256' \
  "$root/crates/proof-compression/src/pipeline/prepare.rs" \
  | sed -n 's/.*"\([0-9a-f]\{64\}\)".*/\1/p')
[ ${#srs_sha256} -eq 64 ] || { echo "IGNITION_SRS_SHA256 not found" >&2; exit 1; }
for d in "$ixvm" "$aggr"; do
  [ -f "$d/key.bin" ] && [ -f "$d/identity.json" ] \
    || { echo "$d lacks key.bin or identity.json" >&2; exit 1; }
done
[ ! -e "$work" ] || { echo "$work exists; give a new directory" >&2; exit 1; }
avail=$(awk '/^MemAvailable:/ {print int($2 / 1000000)}' /proc/meminfo)
need=${MIN_MEM_GB:-120}
[ "$avail" -ge "$need" ] \
  || { echo "only $avail GB of memory available, $need GB needed" >&2; exit 1; }

# Keep Cargo's registry and toolchain, then move everything else into the work dir.
cargo_home=${CARGO_HOME:-$HOME/.cargo}
rustup_home=${RUSTUP_HOME:-$HOME/.rustup}
mkdir -p "$work"/home "$work"/tmp "$work"/target \
  "$work"/params/bn254-ignition-main-197
work=$(cd "$work" && pwd)
exec > >(tee "$work/rederive.log") 2>&1
echo "checkout $(git -C "$root" rev-parse HEAD)," \
  "$(git -C "$root" status --porcelain --untracked-files=no | wc -l) modified files"
srs=$work/params/bn254-ignition-main-197/srs.bin
if [ -n "${IX_RELEASE_SRS:-}" ]; then
  cp "$IX_RELEASE_SRS" "$srs"
else
  curl -fsSL -o "$srs" "$srs_url"
fi
echo "$srs_sha256  $srs" | sha256sum -c -
unset IX_KZG_SRS IX_KZG_SRS_CACHE IX_KZG_FIXED_CACHE IX_KZG_FILECOIN_CACHE \
  IX_KZG_FILECOIN_MANIFEST IX_ROOT
export HOME=$work/home TMPDIR=$work/tmp IX_PARAMS_DIR=$work/params \
  CARGO_HOME=$cargo_home CARGO_TARGET_DIR=$work/target \
  IX_ROOT_VK=$aggr/key.bin IX_IXVM_KEY_DIR=$ixvm IX_AGGR_KEY_DIR=$aggr
if [ -d "$rustup_home" ]; then export RUSTUP_HOME=$rustup_home; fi

cd "$root"
timed=()
if /usr/bin/time -v true >/dev/null 2>&1; then timed=(/usr/bin/time -v); fi
run_tests() {
  "${timed[@]}" cargo test --release --locked -p ix-proof-compression \
    --no-default-features --features parallel,plonk --lib -- "$@"
}
run_tests --exact \
  pipeline::verifying_keys::tests::bundled_release_files_match_their_pins \
  pipeline::derive::tests::release_plonk_description_matches_its_pin
run_tests --ignored --exact \
  pipeline::verifying_keys::tests::release_prefix_matches_the_release_keys
run_tests --ignored --exact --nocapture \
  pipeline::derive::tests::release_recursive_key_derives_without_a_proof
echo "release keys re-derived from a clean state: every pin holds"
