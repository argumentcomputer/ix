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
# that fix the verifying keys (`compiledArtifact` and the `ixvm` and
# `stark-export` exporters with their Aiur sources). `lake exe verify-path`
# (Tests/VerifyPath.lean) hashes the kernel declarations of every constant
# reachable from those entry points, outside the Lean toolchain, plus the
# Aiur source bundles, and this script compares the result with the pin in
# tools/verify-path.fingerprint. The roots and closure sizes are listed at the
# top of the pin.
#
# Out of scope: Rust. The STARK verifier behind `Ix.FormalProver.verify`
# (`rs_formal_verify` in crates/ffi/src/formal.rs, `crates/ix-prover`,
# `crates/stark-verifier`, `crates/aiur` and the multi-stark crate), the key
# derivation behind `Ix.FormalProver.identity`, and the legacy verifier FFI
# reached by `ix verify --legacy`. Only the Lean side of those calls (their
# `@[extern]` symbols and types) is fingerprinted.
#
# Updating the pin. A mismatch means the acceptance path changed. Do not
# update the pin to make this script pass: a human must review the listed
# constants, and the new pin goes in a commit of its own whose message says
# why the acceptance path changed. Regenerate it with
#   tools/check-verify-path.sh --update
#
# Usage: tools/check-verify-path.sh [--update]
set -euo pipefail
cd "$(dirname "$0")/.."

pin=tools/verify-path.fingerprint
lake build verify-path +Ix.Cli.CatalogAggregate +Ix.Cli.FormalAggregate +Ix.Cli.FormalAiur \
  +Ix.Cli.VerifyCmd +IxVM.Main +MultiStark.Main >/dev/null
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
lake exe verify-path > "$actual"

if [[ ${1:-} == --update ]]; then
  cp "$actual" "$pin"
  echo "updated $pin: $(head -1 "$pin")"
  echo "commit it on its own, after review, with the reason the acceptance path changed"
  exit 0
fi

if cmp -s "$pin" "$actual"; then
  echo "verify path unchanged: $(head -1 "$pin")"
  exit 0
fi

echo "VERIFY PATH CHANGED: the Lean code that accepts formal proofs differs from $pin" >&2
echo "  pinned: $(head -1 "$pin")" >&2
echo "  actual: $(head -1 "$actual")" >&2
echo >&2
# Constants are `<hash> <group>:<name>`; other lines are the header.
awk '
  FNR == 1 { file++ }
  $1 == "fingerprint" { next }
  $1 ~ /^[0-9a-f]{64}$/ && NF == 2 { h[file, $2] = $1; names[$2]; next }
  { header[file, $0] = 1; lines[$0] }
  END {
    for (n in names) {
      if (!((2, n) in h)) print "added:   " n
      else if (!((1, n) in h)) print "removed: " n
      else if (h[1, n] != h[2, n]) print "changed: " n
    }
    for (l in lines) {
      if (!((2, l) in header)) print "header+: " l
      else if (!((1, l) in header)) print "header-: " l
    }
  }' "$actual" "$pin" | sort >&2
echo >&2
echo "Review the change. If it is intended, update the pin in a separate commit (see the header of $0)." >&2
exit 1
