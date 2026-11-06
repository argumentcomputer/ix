#!/usr/bin/env bash
# Verify-path gate: fails when the Lean code that accepts formal Aiur proofs
# changes.
#
# What it protects. A formal root is accepted by `ix verify` (formal,
# `--aggregate` and `--aggregate --ixc`), and a root the aggregate controller
# returns by `accept`, `acceptSlot` and `acceptCatalog`. Their soundness rests
# on Lean code: the environment's role binding and claim context
# (`withDefaultRoleBinding`, `Ix.ClaimContext.ofEnv`), the expected root
# statement (`Aggr.Reference.expectedSlotsFromManifest`, `CheckEnvTrees.join`,
# `joinStructural`, `AssumptionTree`, `Ix.Shard.shardsCover`,
# `envCanonicalTree`), the catalog's root (`catalogMembers`, `catalogPlan`),
# the binding-proof check, the coverage audit (`auditAggregateConstants`),
# the public input (`Aggr.allowedBlob`, `Aggr.pubInput`), the wrapper check
# (`verifyWrapper`), and the export and caching of the certified artifacts
# that fix the verifying keys (`compiledArtifact`, the compiler linked into
# `ix` (`Ix.FormalCompiler`), and the `ixvm` and `stark-export` exporters
# with their Aiur sources), and the pinned verifying keys acceptance requires
# (tools/formal-aiur.keys, `Ix.Cli.FormalKeys`). `lake exe verify-path`
# (Tests/VerifyPath.lean) hashes the kernel declarations of every constant
# reachable from those entry points, outside the Lean toolchain, plus the
# Aiur source bundles and the key pins, into one fingerprint. The pin,
# tools/verify-path.fingerprint, holds that fingerprint with the roots,
# closure sizes and source hashes; the per-constant hashes are not committed.
#
# Out of scope: Rust. The STARK verifier behind `Ix.FormalProver.verify`
# (`rs_formal_verify` in crates/ffi/src/formal.rs, `crates/ix-prover`,
# `crates/stark-verifier`, `crates/aiur` and the multi-stark crate), the key
# derivation behind `Ix.FormalProver.identity`, and the legacy verifier FFI
# reached by `ix verify --legacy`. Only the Lean side of those calls (their
# `@[extern]` symbols and types) is fingerprinted.
#
# Updating the pin. A mismatch means the acceptance path changed. Do not
# update the pin to make this script pass: a human must review which
# constants changed, and the new pin goes in a commit of its own whose
# message says why the acceptance path changed. `--list` prints every
# constant's hash; run it on the base revision and on the change, and diff
# the two. Regenerate the pin with
#   tools/check-verify-path.sh --update
#
# Usage: tools/check-verify-path.sh [--update | --list]
set -euo pipefail
cd "$(dirname "$0")/.."

pin=tools/verify-path.fingerprint
lake build verify-path +Ix.Cli.CatalogAggregate +Ix.Cli.FormalAggregate +Ix.Cli.FormalAiur \
  +Ix.Cli.VerifyCmd +Ix.FormalCompiler +IxVM.Main +MultiStark.Main >/dev/null
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
lake exe verify-path > "$actual"

if [[ ${1:-} == --list ]]; then
  cat "$actual"
  exit 0
fi

# Constants are `<hash> <group>:<name>`; every other line is the pinned header.
header() { grep -Ev '^[0-9a-f]{64} [^ ]+$' "$1"; }

if [[ ${1:-} == --update ]]; then
  header "$actual" > "$pin"
  echo "updated $pin: $(head -1 "$pin")"
  echo "commit it on its own, after review, with the reason the acceptance path changed"
  exit 0
fi

if header "$actual" | cmp -s "$pin" -; then
  echo "verify path unchanged: $(head -1 "$pin")"
  exit 0
fi

echo "VERIFY PATH CHANGED: the Lean code that accepts formal proofs differs from $pin" >&2
diff "$pin" <(header "$actual") | sed -n 's/^< /  pinned: /p; s/^> /  actual: /p' >&2 || true
echo >&2
echo "The fingerprint covers every constant on the path. To see which changed, run" >&2
echo "\`$0 --list\` here and on the base revision and diff the outputs. If the change" >&2
echo "is intended, update the pin in a separate commit (see the header of $0)." >&2
exit 1
