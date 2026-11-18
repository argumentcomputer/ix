#!/usr/bin/env bash
# cargo with the multi-stark fork that has shared fixed slots
# (`System::new_shared`, branch formal-aiur/shared-fixed) patched over the
# pinned upstream multi-stark, and ix-proof-compression's `shared-fixed`
# feature enabled. The pin in Cargo.toml stays upstream; the patch exists only
# for this command.
#
#   tools/cargo-shared-fixed.sh <cargo subcommand> [args...]
#   e.g. tools/cargo-shared-fixed.sh test -p ix-proof-compression --release --test aiur_template_v2
#
# IX_MULTI_STARK_FORK overrides the fork's path (default
# ~/repos/forks/multi-stark-shared-fixed). Cargo records the patched source
# in Cargo.lock while it runs; the lockfile is restored afterwards, so builds
# without this script keep resolving the upstream pin.
#
# Without this script every build uses the pinned multi-stark: the L3 narrow
# stage shares no fixed slot, so it builds and proves the same system either
# way. The tests that need shared slots are skipped: the two-shard tests of
# `aiur_template_v2` by `cfg(feature = "shared-fixed")` (its one-shard tests
# run), and `aiur_kzg_packed_shared_fixed` by its required feature.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
fork=${IX_MULTI_STARK_FORK:-$HOME/repos/forks/multi-stark-shared-fixed}
[ -f "$fork/Cargo.toml" ] || { echo "multi-stark fork not found at $fork" >&2; exit 1; }
[ $# -ge 1 ] || { echo "usage: $0 <cargo subcommand> [args...]" >&2; exit 2; }
sub=$1; shift
lock=$(mktemp)
cp "$root/Cargo.lock" "$lock"
restore() { cmp -s "$lock" "$root/Cargo.lock" || cp "$lock" "$root/Cargo.lock"; rm -f "$lock"; }
trap restore EXIT
cd "$root"
cargo "$sub" \
  --config "patch.\"https://github.com/argumentcomputer/multi-stark.git\".multi-stark.path=\"$fork\"" \
  --features ix-proof-compression/shared-fixed "$@"
