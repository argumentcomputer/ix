#!/usr/bin/env bash
# Verifying-key gate: fails when the certified formal Aiur programs' keys
# differ from the committed pins.
#
# What it protects. tools/formal-aiur.keys pins, for the IxVM, recursive
# verifier and aggregation programs, the program identity (the content
# digest of the compiled artifact) and the BLAKE3 digest of the verifying key
# under the default STARK parameters. `ix verify` and the aggregate
# acceptance check (`Ix.Cli.FormalAggregate.context`, `accept`) embed the pins
# and reject keys that differ, and aggregate proofs commit to the pinned IxVM
# and aggregation keys. `lake exe formal-keys` (Tests/FormalKeys.lean)
# derives the pin file from the checkout's programs, compiling any missing
# from the compiled-program cache, and this script compares it with the
# committed file.
#
# Updating the pins. A mismatch means the compiled circuits or programs
# changed. Do not update the pins to make this script pass: review the change,
# then commit the new pins on their own, saying why the circuits changed.
# Regenerate them with
#   tools/check-formal-keys.sh --update
# The pin file is part of the verify-path fingerprint, so tools/check-verify-path.sh
# then needs its re-pin review too.
#
# Usage: tools/check-formal-keys.sh [--update]
set -euo pipefail
cd "$(dirname "$0")/.."

pin=tools/formal-aiur.keys
lake build formal-keys >/dev/null
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
lake exe formal-keys > "$actual"

if [[ ${1:-} == --update ]]; then
  cp "$actual" "$pin"
  echo "updated $pin"
  echo "commit it on its own, after review, with the reason the circuits changed"
  exit 0
fi

if cmp -s "$pin" "$actual"; then
  echo "verifying keys match $pin"
  exit 0
fi

echo "VERIFYING KEYS CHANGED: the certified programs differ from $pin" >&2
diff "$pin" "$actual" >&2 || true
echo >&2
echo "Review the change. If it is intended, update the pins in a separate commit (see the header of $0)." >&2
exit 1
